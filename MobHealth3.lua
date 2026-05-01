--[[
    MobHealth3 - Kronos Edition (modern client)

    Maintained by Mirasu of Kronos. Modernized for the 1.14.x Classic Era
    client while talking to a TrinityCore 1.12 server (Kronos) via proxy.

    Kronos sends real health for friendly party/raid units, percentages for
    everyone else. This addon fills the gap: static DB for known NPCs,
    combat-log accumulator for players and unlisted mobs.
--]]

-- Captured BEFORE anything else can replace these. The Luna/oUF bridge
-- below needs the real Blizzard implementations to avoid recursing into
-- its own wrappers.
local origUnitHealth    = UnitHealth
local origUnitHealthMax = UnitHealthMax

-- Static database (populated by Data.lua). Claim without overwriting.
MobHealth3_StaticDB = MobHealth3_StaticDB or {}

-- Name-only index over MobHealth3_StaticDB, built lazily on first lookup.
-- The legacy fallback was a `pairs()` scan over ~10K entries with a regex
-- compiled inside the loop — fine for solo PvE, brutal at 80v80 where every
-- unlisted player and NPC triggers the full scan on every UnitHealth call
-- (potentially millions of iterations per second once you factor in Luna,
-- EasyFrames, Blizzard frames, and nameplates all calling through us).
-- This makes the name-only fallback O(1) and turns "not in DB" into a
-- single hash miss instead of 10K wasted iterations.
--
-- Lazy: Data.lua loads AFTER MobHealth3.lua per the TOC, so the table is
-- empty when this file runs. Defer the build to first lookup.
local NameIndex

local function lookupByName(name)
    if not name then return nil end
    if not NameIndex then
        NameIndex = {}
        for key, val in pairs(MobHealth3_StaticDB) do
            local nameOnly = string.match(key, "^([^:]+)")
            if nameOnly and not NameIndex[nameOnly] then
                NameIndex[nameOnly] = val
            end
        end
    end
    return NameIndex[name]
end

-- Persisted snapshots of converged accumulator estimates, keyed by
-- "name:level". Loaded once per session; updated as the accumulator finds
-- (or refutes) values during combat.
MobHealth3SavedDB           = MobHealth3SavedDB or {}
MobHealth3SavedDB.estimates = MobHealth3SavedDB.estimates or {}

local MH3Cache         = {}
local AccumulatorHP    = {}
local AccumulatorPerc  = {}

local currentAccHP, currentAccPerc
local targetName, targetLevel, targetGUID, targetIndex
local recentDamage, recentHealing = 0, 0
local startPercent, lastPercent = 100, 100

-- Per-class baseline HP-per-level for the Plausibility Filter
local ClassHPMultipliers = {
    MAGE = 55, PRIEST = 60, ROGUE = 65, HUNTER = 70, DRUID = 70,
    SHAMAN = 75, PALADIN = 80, WARLOCK = 80, WARRIOR = 90,
}

-- Legacy MobHealth/MobHealth2 read contract: lookup by "name:level" with
-- fallbacks, return a "max/100" string so callers can extract the max HP.
local compatMT = {
    __index = function(t, k)
        local val = rawget(t, k)
                 or rawget(t, string.gsub(tostring(k), ":%d+$", ":63"))
                 or rawget(t, string.gsub(tostring(k), ":%d+$", ""))
        if val then
            local _, _, health = string.find(tostring(val), ".+/(%d+)")
            return (health or val) .. "/100"
        end
    end,
}

MobHealthDB  = setmetatable(MobHealth3_StaticDB, compatMT)
MobHealth3DB = MobHealthDB

if pfUI and pfUI.api then
    pfUI.api.libmobhealth = MobHealthDB
end

-- Sniff frame: legacy addons probe for this name to detect MH/MH2/MI2.
CreateFrame("Frame", "MobHealthFrame")

function GetMH3Cache() return MH3Cache end

local MobHealth3 = CreateFrame("Frame", "MobHealth3Frame")
_G.MobHealth3 = MobHealth3

-- Kronos sends real HP only for units in your party/raid (and yourself/pet).
-- Everyone else (target, mouseover, nameplates, enemy players, NPCs) comes
-- through as a 0..100 percentage with UnitHealthMax ≈ 100. Distinguish by
-- unit token, not by the max value — a percentage unit at full HP looks
-- identical to a friendly with real max=100, so value-based heuristics fail.
--
-- Indirect tokens (`target`, `mouseover`, `focus`) need a second check:
-- if your target IS yourself / your pet / a party member, the server still
-- sends real HP for it. Without UnitIsUnit/UnitInParty fallback we'd route
-- self-targets through the estimator and produce garbage like "60 / 80".
local function isFriendlyRealUnit(unit)
    if not unit then return false end
    if unit == "player" or unit == "pet" or unit == "vehicle" then return true end
    if string.find(unit, "^party") or string.find(unit, "^raid") then return true end
    if UnitIsUnit(unit, "player") or UnitIsUnit(unit, "pet") then return true end
    if UnitInParty(unit) or UnitInRaid(unit) then return true end
    return false
end

----------------------------------------------------------------
-- The unified engine
----------------------------------------------------------------
function MobHealth3:GetUnitHealth(unit, current, max, uName, uLevel)
    if type(unit) == "table" then
        unit, current, max, uName, uLevel = current, max, uName, uLevel, nil
    end
    if not UnitExists(unit) then return 0, 0, false end

    -- Always read raw values from the server, not our bridged wrapper.
    -- Otherwise the global override would loop us back through the estimator.
    current = current or origUnitHealth(unit)
    max     = max     or origUnitHealthMax(unit)
    uName   = uName   or UnitName(unit)
    uLevel  = uLevel  or UnitLevel(unit)

    -- Server gave real values: pass through. Only friendly party/raid units
    -- get real HP from Kronos; everyone else comes through as 0..100 with
    -- max≈100, so we can't distinguish by value alone.
    if isFriendlyRealUnit(unit) then return current, max, true end

    local uKey = uName .. ":" .. uLevel
    local db   = MobHealth3_StaticDB
    local rawData

    if uLevel ~= -1 then
        rawData = rawget(db, uKey)
    end
    if not rawData then
        rawData = lookupByName(uName)
    end

    if rawData then
        local _, _, dbLevel, dbMax = string.find(tostring(rawData), "(%d+)/(%d+)")
        local finalMax    = tonumber(dbMax or rawData)
        local sourceLevel = tonumber(dbLevel or uLevel)

        if finalMax and finalMax > 50 then
            if uLevel > 0 and sourceLevel > 0 and uLevel ~= sourceLevel then
                finalMax = math.floor(finalMax * (uLevel / sourceLevel))
            end
            return math.floor((current/100) * finalMax + 0.5), finalMax, true
        end
    end

    -- Combat-derived estimator (players & unlisted NPCs).
    -- Three sources, in order of trust:
    --   1. Fresh accumulator with accPerc >= 5  → strong, overrides snapshot
    --   2. Saved snapshot from a prior session  → instant "good guess" while
    --      this session's accumulator builds up; gets refuted/replaced once
    --      fresh data accumulates past the divergence threshold
    --   3. Low-confidence percentage fallback   → no real data yet
    local accHP   = AccumulatorHP[uKey]
    local accPerc = AccumulatorPerc[uKey]
    local saved   = MobHealth3SavedDB.estimates[uKey]

    local estimatedMax
    local fromAccumulator = false

    if accHP and accPerc and accPerc >= 5 then
        estimatedMax    = math.floor((accHP / accPerc) * 100 + 0.5)
        fromAccumulator = true
    elseif saved and saved > 50 then
        estimatedMax = saved
    end

    if estimatedMax then
        if UnitIsPlayer(unit) and uLevel > 0 then
            local sanityCap   = uLevel * 130
            local sanityFloor = uLevel * 30
            if estimatedMax > sanityCap or estimatedMax < sanityFloor then
                local _, class = UnitClass(unit)
                estimatedMax = uLevel * (ClassHPMultipliers[class] or 65)
            end
        end

        if estimatedMax > 50 then
            -- Persist the fresh estimate. Update if it's new, or if the
            -- saved snapshot is stale by >25% (gear change, level-up,
            -- talent respec — common in PvP). Small drift gets coalesced
            -- to avoid SV churn from per-frame ratio noise.
            if fromAccumulator then
                local diff = saved and math.abs(estimatedMax - saved) / saved or 1
                if not saved or diff > 0.05 then
                    MobHealth3SavedDB.estimates[uKey] = estimatedMax
                end
            end

            local estimatedCurrent = math.floor((current/100) * estimatedMax + 0.5)
            MH3Cache[uKey] = estimatedMax
            return estimatedCurrent, estimatedMax, true
        end
    end

    -- Have *some* fresh data but not enough yet → percentage fallback.
    if accHP and accPerc and accPerc > 0 then
        return current, 100, true
    end

    return current, max, false
end

----------------------------------------------------------------
-- Accumulator: each percent the target loses, attribute the damage we saw
-- since the last tick. accHP / accPerc * 100 = estimated max.
----------------------------------------------------------------
local function calculateMaxHealth(current, max)
    if current == 0 then return end  -- target dead

    -- Resurrect / transform anomaly — re-baseline.
    if startPercent > 100 then
        startPercent = current
        lastPercent  = current
        recentDamage, recentHealing = 0, 0
        return
    end

    local deltaPerc  = lastPercent - current      -- + = HP went down
    local netChange  = recentDamage - recentHealing  -- + = HP went down
    if deltaPerc == 0 then return end

    -- HP changed but we tracked nothing for this target (damage from a
    -- source we don't see, or events we filtered out). Don't pollute
    -- the accumulator — just re-baseline lastPercent.
    if netChange == 0 then
        lastPercent = current
        return
    end

    -- Signs must agree: tracked damage requires HP to drop, tracked heal
    -- requires HP to rise. Disagreement means our visibility is incomplete
    -- (e.g., tracked a tiny heal but they got bombed by a DOT we missed).
    -- Discard the sample rather than corrupt the ratio.
    if (netChange > 0) ~= (deltaPerc > 0) then
        recentDamage, recentHealing = 0, 0
        lastPercent = current
        return
    end

    currentAccHP   = currentAccHP   + math.abs(netChange)
    currentAccPerc = currentAccPerc + math.abs(deltaPerc)
    recentDamage, recentHealing = 0, 0
    lastPercent = current

    AccumulatorHP[targetIndex]   = currentAccHP
    AccumulatorPerc[targetIndex] = currentAccPerc
end

----------------------------------------------------------------
-- Target switching: seed accumulators from static DB or session memory.
----------------------------------------------------------------
local function onTargetChanged()
    -- UnitCanAttack covers hostile mobs, enemy-faction players, AND duel
    -- partners (same-faction but temporarily attackable). Plain
    -- `not UnitIsFriend(...)` excludes duel partners since they remain same
    -- faction; the accumulator would never build for them.
    if UnitExists("target") and not UnitIsDead("target") and UnitCanAttack("player", "target") then
        targetName  = UnitName("target")
        targetLevel = UnitLevel("target")
        targetGUID  = UnitGUID("target")
        targetIndex = string.format("%s:%d", targetName, targetLevel)

        recentDamage, recentHealing = 0, 0
        -- Raw percentage for the estimator baseline.
        startPercent = origUnitHealth("target")
        lastPercent  = startPercent

        currentAccHP   = AccumulatorHP[targetIndex]   or 0
        currentAccPerc = AccumulatorPerc[targetIndex] or 0

        if currentAccHP == 0 then
            local db = MobHealth3_StaticDB
            local rawData

            if targetLevel ~= -1 then
                rawData = rawget(db, targetIndex)
            end
            if not rawData then
                rawData = lookupByName(targetName)
            end

            if rawData then
                local _, _, dbLevel, dbMax = string.find(tostring(rawData), "(%d+)/(%d+)")
                local finalMax    = tonumber(dbMax or rawData)
                local sourceLevel = tonumber(dbLevel or targetLevel)

                if finalMax and finalMax > 50 then
                    if targetLevel > 0 and sourceLevel > 0 and targetLevel ~= sourceLevel then
                        finalMax = math.floor(finalMax * (targetLevel / sourceLevel))
                    end
                    AccumulatorHP[targetIndex]   = finalMax
                    AccumulatorPerc[targetIndex] = 100
                    currentAccHP, currentAccPerc = finalMax, 100
                end
            end
        end

        -- Cap retained sample so a long-running target doesn't drown out new data.
        local maxLimit = UnitIsPlayer("target") and 100 or 200
        if currentAccPerc and currentAccPerc > maxLimit then
            currentAccHP   = (currentAccHP / currentAccPerc) * maxLimit
            currentAccPerc = maxLimit
        end
    else
        currentAccHP, currentAccPerc, targetGUID = nil, nil, nil
    end
end

----------------------------------------------------------------
-- Combat log: tally damage dealt to current target. Modern API, no string parsing.
----------------------------------------------------------------
local function onCombatLogEvent()
    if not currentAccHP or not targetGUID then return end

    -- Capture enough args to read overkill/absorbed for every event variant.
    -- SWING_DAMAGE:        a12 amount, a13 overkill, a17 absorbed
    -- SPELL_*_DAMAGE etc.: a15 amount, a16 overkill, a20 absorbed
    -- ENVIRONMENTAL:       a13 amount, a14 overkill, a18 absorbed
    -- SPELL_HEAL:          a15 amount, a16 overhealing, a17 absorbed
    local _, subevent, _, _, _, _, _,
          destGUID, _, _, _,
          a12, a13, a14, a15, a16, a17, a18, _, a20 = CombatLogGetCurrentEventInfo()

    if destGUID ~= targetGUID then return end

    local amount, overkill, absorbed = 0, 0, 0
    local isHeal = false

    if subevent == "SWING_DAMAGE" then
        amount   = a12 or 0
        overkill = math.max(a13 or 0, 0)
        absorbed = a17 or 0
    elseif subevent == "ENVIRONMENTAL_DAMAGE" then
        amount   = a13 or 0
        overkill = math.max(a14 or 0, 0)
        absorbed = a18 or 0
    elseif subevent == "SPELL_DAMAGE"
        or subevent == "SPELL_PERIODIC_DAMAGE"
        or subevent == "RANGE_DAMAGE"
        or subevent == "DAMAGE_SHIELD"
        or subevent == "DAMAGE_SPLIT" then
        amount   = a15 or 0
        overkill = math.max(a16 or 0, 0)
        absorbed = a20 or 0
    elseif subevent == "SPELL_HEAL" or subevent == "SPELL_PERIODIC_HEAL" then
        -- Heals on the target. a16 is overhealing in this slot.
        amount   = a15 or 0
        overkill = math.max(a16 or 0, 0)
        absorbed = a17 or 0
        isHeal = true
    end

    -- effective = HP actually moved (damage past mitigation, or heal past
    -- overheal/absorb). Absorbs and overkill are both "wasted" relative to
    -- the HP bar, so subtracting them prevents PvP shield-users from
    -- inflating the estimate and stops the killing blow from doing the same.
    local effective = amount - overkill - absorbed
    if effective <= 0 then return end

    if isHeal then
        recentHealing = recentHealing + effective
    else
        recentDamage  = recentDamage  + effective
    end
end

----------------------------------------------------------------
-- Event dispatch
----------------------------------------------------------------
-- Forward decl so the OnEvent closure can see the bridge installer
-- that's defined further down (Lua locals must be declared before use).
local installBridges

MobHealth3:RegisterEvent("PLAYER_LOGIN")
MobHealth3:RegisterEvent("PLAYER_TARGET_CHANGED")
MobHealth3:RegisterEvent("UNIT_HEALTH")
MobHealth3:RegisterEvent("COMBAT_LOG_EVENT_UNFILTERED")

MobHealth3:SetScript("OnEvent", function(self, event, arg1)
    if event == "PLAYER_TARGET_CHANGED" then
        onTargetChanged()
    elseif event == "UNIT_HEALTH" then
        if arg1 == "target" and currentAccHP ~= nil then
            -- Estimator math needs raw 0..100 percentages, not bridged values.
            calculateMaxHealth(origUnitHealth("target"), origUnitHealthMax("target"))
        end
    elseif event == "COMBAT_LOG_EVENT_UNFILTERED" then
        onCombatLogEvent()
    elseif event == "PLAYER_LOGIN" then
        DEFAULT_CHAT_FRAME:AddMessage("|cff00ff00MobHealth3:|r Kronos edition loaded.")
        -- Permanently neutralize the diagnostic overlay from older versions.
        -- It's an unnamed OVERLAY-layer FontString parented somewhere under
        -- TargetFrame. Hide() alone gets undone by some upstream code on
        -- the next frame, so layer multiple defenses: empty the text, set
        -- alpha to 0, shrink to 1×1, and re-anchor far offscreen. Even if
        -- something Shows() it again it has nothing visible to display.
        -- EasyFrames' TextString is on the ARTWORK layer so it's untouched.
        local function killOverlayOrphans(frame, depth)
            if depth > 6 then return end
            if frame.GetRegions then
                for _, region in ipairs({frame:GetRegions()}) do
                    if region.GetObjectType
                       and region:GetObjectType() == "FontString"
                       and not region:GetName()
                       and region.GetDrawLayer
                       and region:GetDrawLayer() == "OVERLAY" then
                        local txt = region:GetText() or ""
                        if txt:find("/") then
                            region:SetText("")
                            region:SetAlpha(0)
                            region:SetWidth(1)
                            region:SetHeight(1)
                            region:ClearAllPoints()
                            region:SetPoint("CENTER", UIParent, "BOTTOMLEFT", -9999, -9999)
                            region:Hide()
                        end
                    end
                end
            end
            if frame.GetChildren then
                for _, child in ipairs({frame:GetChildren()}) do
                    killOverlayOrphans(child, depth + 1)
                end
            end
        end
        if TargetFrame then killOverlayOrphans(TargetFrame, 0) end

        -- Also neutralize the named MobHealth3TargetText FontString from
        -- previous versions that experimented with a centered overlay on
        -- the bar. EasyFrames provides target numbers when the user has
        -- Blizzard's status text option enabled — we don't want to double
        -- them up.
        if _G.MobHealth3TargetText then
            _G.MobHealth3TargetText:SetText("")
            _G.MobHealth3TargetText:SetAlpha(0)
            _G.MobHealth3TargetText:Hide()
        end

        installBridges()
    end
end)

-- No OnUpdate by design. We previously force-synced TargetFrameHealthBar's
-- range/value and Blizzard nameplate bars from a 5/sec OnUpdate, but those
-- insecure writes tainted the TargetFrame chain — Blizzard's stock
-- TargetFrame_OnUpdate propagates that taint into TargetofTarget_Update
-- and the protected TargetFrameToT:Show() gets blocked, breaking ToT.
-- Bar fills end up correct anyway because the bridge keeps cur/max in
-- proportion whether max is 100 (raw percentage) or 4800 (estimated real),
-- and frame addons read UnitHealth via the global override for text.

----------------------------------------------------------------
-- Legacy public API (MobHealth / MobHealth2 contracts)
----------------------------------------------------------------
function MobHealth_GetTargetMaxHP()
    local _, m, found = MobHealth3:GetUnitHealth("target")
    return found and m or nil
end

function MobHealth_GetTargetCurHP()
    local c, _, found = MobHealth3:GetUnitHealth("target")
    return found and c or nil
end

function MobHealth_PPP(index)
    return MH3Cache[index] and MH3Cache[index]/100 or 0
end

----------------------------------------------------------------
-- Bridge: route the world's UnitHealth/UnitHealthMax calls through us.
--
-- Strategy: replace _G.UnitHealth / _G.UnitHealthMax with wrappers that
-- short-circuit when the server already provided real values (max > 50)
-- and otherwise route through MobHealth3:GetUnitHealth for an estimate.
-- Threshold is 50 (not 100) because low-level mobs have real maxes well
-- under 100 (e.g. level-1 critters around 42 HP).
--
-- This single global override fixes:
--   * Default Blizzard frames (TargetFrame, etc.)
--   * EasyFrames text formats (calls UnitHealth inside Utils.UpdateHealthValues)
--   * Kui nameplates and any other addon reading UnitHealth
--   * oUF's loadstring'd tags (perhp, missinghp) via _PROXY's __index = _G
--
-- Direct C-function references captured into local tables (notably
-- oUF's curhp/maxhp at tags.lua:371-373) are NOT affected by global
-- replacement, so we still patch those entries explicitly below.
----------------------------------------------------------------
local function bridgedHealth(unit)
    if not unit or not UnitExists(unit) then return 0 end
    local cur = origUnitHealth(unit)
    local max = origUnitHealthMax(unit)
    if isFriendlyRealUnit(unit) then return cur end
    local c, m, found = MobHealth3:GetUnitHealth(unit, cur, max)
    if found and m > 50 then return c end
    return cur
end

local function bridgedHealthMax(unit)
    if not unit or not UnitExists(unit) then return 0 end
    local cur = origUnitHealth(unit)
    local max = origUnitHealthMax(unit)
    if isFriendlyRealUnit(unit) then return max end
    local c, m, found = MobHealth3:GetUnitHealth(unit, cur, max)
    if found and m > 50 then return m end
    return max
end

-- Per-function patcher. Replaces UnitHealth / UnitHealthMax inside one
-- specific function via setfenv, so callers of that function see bridged
-- values without us touching the global table. The wrapping metatable
-- delegates everything else (other globals, locals) to the original env.
local function patchAddonFunc(fn)
    if type(fn) ~= "function" then return end
    local env = getfenv(fn)
    if type(env) ~= "table" then return end
    local newEnv = setmetatable({
        UnitHealth    = bridgedHealth,
        UnitHealthMax = bridgedHealthMax,
    }, {__index = env})
    pcall(setfenv, fn, newEnv)
end

-- Tag-environment patcher for addons whose loadstring'd tags are
-- setfenv'd to a private env table (Luna, SUF). Writing UnitHealth
-- directly on the env shadows the env's `__index = _G` fallback for
-- every tag that shares the env.
--
-- IMPORTANT: use rawset, not direct assignment. SUF's TagEnv has a
-- `__newindex` metamethod that silently redirects writes to `_G` —
-- which is precisely the global-override-tainting behavior we need
-- to avoid. rawset bypasses `__newindex` and writes directly to the
-- env table, so the bridge is local to that env only.
local function patchTagEnv(tagFn)
    if type(tagFn) ~= "function" then return nil end
    local env = getfenv(tagFn)
    if type(env) ~= "table" then return nil end
    rawset(env, "UnitHealth",    bridgedHealth)
    rawset(env, "UnitHealthMax", bridgedHealthMax)
    return env
end

local bridgesInstalled = false
installBridges = function()
    if bridgesInstalled then return end

    -- We deliberately do NOT replace _G.UnitHealth / _G.UnitHealthMax.
    -- Blizzard's secure TargetFrame_OnUpdate calls UnitHealth on every
    -- frame; if the global points at our insecure wrapper, the entire
    -- secure call chain becomes tainted and Blizzard's protected
    -- TargetFrameToT:Show() gets blocked, breaking ToT in combat.
    -- Instead we detect the user's primary unit-frame addon and patch
    -- *only that one*. Bridged values stay inside that addon's own
    -- (insecure) execution and never leak into Blizzard's secure chain.
    --
    -- Priority order (a typical user runs one of these as their primary):
    --   Luna  >  ShadowedUnitFrames  >  pfUI  >  EasyFrames  >  (none)
    -- The first match installs and we stop. If the user has none of
    -- these, no bridge is installed and addons see raw server values.

    local bridged

    local lunaOUF = (LUF and LUF.oUF) or oUF
    if lunaOUF and lunaOUF.TagsWithHeal and lunaOUF.TagsWithHeal.Methods then
        -- Luna Unit Frames: patch the shared TagsWithHeal env so every
        -- HP tag (smarthealth, curhp, maxhp, perhp, etc.) resolves
        -- UnitHealth through our bridge. Also force UnitHasHealthData
        -- true so duel partners / BG-PvP enemies show real numbers
        -- instead of falling into the "X%" branch.
        local env = patchTagEnv(lunaOUF.TagsWithHeal.Methods.smarthealth)
        if env then
            env.UnitHasHealthData = function() return true end
            bridged = "Luna Unit Frames"
        end
    end

    if not bridged and ShadowUF then
        -- ShadowedUnitFrames: patch its private TagEnv (used for all
        -- loadstring'd tag display) plus the Health module's Update
        -- (which sets the bar fill itself).
        --
        -- Timing: SUF's tagFunc metamethod can return `false` at
        -- PLAYER_LOGIN if the defaultTags table from modules/tags.lua
        -- isn't wired in yet. We try immediately and also schedule a
        -- delayed retry; rawset is idempotent so re-running is safe.
        local function applySUFPatch()
            if ShadowUF.tagFunc then
                patchTagEnv(ShadowUF.tagFunc.maxhp)
            end
            if ShadowUF.modules and ShadowUF.modules.healthBar then
                patchAddonFunc(ShadowUF.modules.healthBar.Update)
            end
        end
        applySUFPatch()
        if C_Timer and C_Timer.After then
            C_Timer.After(2, applySUFPatch)
        end
        bridged = "ShadowedUnitFrames"
    end

    if not bridged and pfUI and pfUI.api and pfUI.api.tags then
        -- pfUI: direct tag-table assignment, also expose the static DB.
        pfUI.api.tags["curhp"] = bridgedHealth
        pfUI.api.tags["maxhp"] = bridgedHealthMax
        bridged = "pfUI"
    end

    if not bridged and IsAddOnLoaded and IsAddOnLoaded("ModernTargetFrame") then
        -- ModernTargetFrame: SDPhantom's re-skin creates Blizzard-style
        -- TextString/LeftText/RightText FontStrings on TargetFrameHealthBar
        -- and TargetFrameManaBar, then leans on Blizzard's stock
        -- TextStatusBar_UpdateTextString to populate them. The bar's
        -- numeric value comes from UnitHealth (server percentage), so the
        -- default text reads "75 / 100" for percentage-only targets.
        --
        -- Post-hook the update function and rewrite the text widgets with
        -- our bridged values. hooksecurefunc is taint-safe — the hook
        -- runs in insecure context after Blizzard's secure call returns,
        -- so SetText on the FontStrings (which aren't protected widgets)
        -- doesn't leak back into Blizzard's chain.
        local function substituteText(bar)
            if not bar or bar ~= TargetFrameHealthBar or not bar.unit then return end
            local c, m, found = MobHealth3:GetUnitHealth(bar.unit)
            if not found then return end
            if bar.TextString then bar.TextString:SetText(c .. " / " .. m) end
            if bar.LeftText  then bar.LeftText:SetText(c) end
            if bar.RightText then bar.RightText:SetText(m) end
        end
        if hooksecurefunc then
            hooksecurefunc("TextStatusBar_UpdateTextString", substituteText)
        end
        bridged = "ModernTargetFrame"
    end

    if not bridged and IsAddOnLoaded and IsAddOnLoaded("EasyFrames") then
        -- EasyFrames: registers itself via Ace3 (NewAddon) — it's a local
        -- in its own file, not a global. Fetch via LibStub. Then patch
        -- the text formatter via setfenv. The hook runs in post-hook
        -- (insecure) context so bridge calls don't leak taint into
        -- Blizzard's secure chain.
        local EF = LibStub
            and LibStub("AceAddon-3.0", true)
            and LibStub("AceAddon-3.0"):GetAddon("EasyFrames", true)
        if EF and EF.Utils then
            patchAddonFunc(EF.Utils.UpdateHealthValues)
            patchAddonFunc(EF.Utils.UpdateManaValues)
            bridged = "EasyFrames"
        end
    end

    if not bridged and TargetFrameHealthBar then
        -- Stock Blizzard fallback. Classic Era's TargetFrameHealthBar has
        -- no built-in text widget, so we create one and drive it from
        -- UNIT_HEALTH / PLAYER_TARGET_CHANGED events. Visibility is gated
        -- on the user's `statusText` cvar so the addon respects the
        -- "Status Text" Interface option instead of forcing numbers.
        local container = CreateFrame("Frame", nil, TargetFrame)
        container:SetAllPoints(TargetFrameHealthBar)
        container:SetFrameLevel(TargetFrameHealthBar:GetFrameLevel() + 5)
        local fs = container:CreateFontString(
            "MobHealth3StockTargetText", "OVERLAY", "GameFontHighlightSmall")
        fs:SetPoint("CENTER", container, "CENTER", 0, 0)

        local function refresh()
            local cvar = GetCVar and GetCVar("statusText")
            if cvar ~= "1" or not UnitExists("target") then
                fs:SetText("")
                return
            end
            local c, m, found = MobHealth3:GetUnitHealth("target")
            if found then
                fs:SetText(c .. " / " .. m)
            else
                fs:SetText("")
            end
        end

        local watcher = CreateFrame("Frame")
        watcher:RegisterEvent("PLAYER_TARGET_CHANGED")
        watcher:RegisterEvent("UNIT_HEALTH")
        watcher:RegisterEvent("UNIT_MAXHEALTH")
        watcher:RegisterEvent("CVAR_UPDATE")
        watcher:SetScript("OnEvent", function(_, event, arg1)
            if event == "UNIT_HEALTH" or event == "UNIT_MAXHEALTH" then
                if arg1 ~= "target" then return end
            end
            refresh()
        end)
        refresh()

        bridged = "stock Blizzard frames"
    end

    if bridged then
        DEFAULT_CHAT_FRAME:AddMessage(
            "|cff00ff00MobHealth3:|r bridge active for " .. bridged .. ".")
    else
        DEFAULT_CHAT_FRAME:AddMessage(
            "|cff00ff00MobHealth3:|r no target frame available; values " ..
            "will pass through unbridged.")
    end

    bridgesInstalled = true
end

----------------------------------------------------------------
-- Slash commands
----------------------------------------------------------------
SLASH_MOBHEALTH31 = "/mobhealth3"
SLASH_MOBHEALTH32 = "/mh3"
SlashCmdList["MOBHEALTH3"] = function(msg)
    DEFAULT_CHAT_FRAME:AddMessage("|cff00ff00MobHealth3:|r Static DB loaded; combat estimator active.")
    if targetName then
        DEFAULT_CHAT_FRAME:AddMessage(string.format("  Target: %s (lvl %s)  accHP=%s  accPerc=%s",
            tostring(targetName), tostring(targetLevel),
            tostring(currentAccHP), tostring(currentAccPerc)))
    end
end
