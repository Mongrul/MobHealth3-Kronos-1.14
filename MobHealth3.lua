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
        installBridges()
    end
end)

----------------------------------------------------------------
-- Target frame text overlay (throttled to ~5/sec)
----------------------------------------------------------------
local throttle = 0
MobHealth3:SetScript("OnUpdate", function(self, elapsed)
    throttle = throttle + elapsed
    if throttle < 0.2 then return end
    throttle = 0

    if TargetFrame and TargetFrame:IsVisible() then
        local c, m, found = MobHealth3:GetUnitHealth("target")
        if found then
            if not MH3_TargetOverlay then
                MH3_TargetOverlay = TargetFrame:CreateFontString(nil, "OVERLAY", "GameFontNormal")
                MH3_TargetOverlay:SetPoint("CENTER", TargetFrame, "TOPLEFT", 150, -38)
            end
            MH3_TargetOverlay:SetText(c .. " / " .. m)
            MH3_TargetOverlay:Show()

            -- Force-sync TargetFrameHealthBar's range, but only when it
            -- actually disagrees with the bridge. Blizzard never fires
            -- UNIT_MAXHEALTH for percentage-only targets (server max stays
            -- at 100), so switching from a friendly (max=4724) to a
            -- percentage target (max=100) leaves the bar's range stuck and
            -- SetValue gets clamped. Repairing on every tick would race
            -- with Blizzard's text-update flow and drown out EasyFrames'
            -- hook on TextStatusBar_UpdateTextString — only intervene when
            -- a fix is actually needed.
            if TargetFrameHealthBar and TargetFrameHealthBar.unit == "target" then
                local _, currentMax = TargetFrameHealthBar:GetMinMaxValues()
                if math.abs((currentMax or 0) - m) > 0.5 then
                    TargetFrameHealthBar:SetMinMaxValues(0, m)
                end
                if math.abs((TargetFrameHealthBar:GetValue() or 0) - c) > 0.5 then
                    TargetFrameHealthBar:SetValue(c)
                end
                -- Force a text refresh. Blizzard only fires
                -- TextStatusBar_UpdateTextString from UNIT_HEALTH events,
                -- and those are unreliable in 2-box / cross-client scenarios
                -- (party member's HP changes on the other client don't
                -- always wake an event on this one). Calling it manually
                -- triggers EasyFrames' SecureHook so its formatted text
                -- re-reads UnitHealth via our bridge.
                if TextStatusBar_UpdateTextString then
                    TextStatusBar_UpdateTextString(TargetFrameHealthBar)
                end
            end
        elseif MH3_TargetOverlay then
            MH3_TargetOverlay:Hide()
        end
    end

    -- Sync default Blizzard nameplate bars. Same problem as TargetFrame:
    -- Blizzard updates SetValue on UNIT_HEALTH but only refreshes the
    -- range on UNIT_MAXHEALTH (which never fires for percentage units),
    -- so SetValue(3277) on a (0, 100) bar clamps to full and the plate
    -- looks stuck. Bridged values keep cur/max in proportion.
    if C_NamePlate and C_NamePlate.GetNamePlates then
        for _, plate in pairs(C_NamePlate.GetNamePlates()) do
            local frame = plate.UnitFrame
            if frame and frame.unit then
                local hb = frame.healthBar or frame.HealthBar
                if hb then
                    local pc, pm, pfound = MobHealth3:GetUnitHealth(frame.unit)
                    if pfound then
                        local _, plateMax = hb:GetMinMaxValues()
                        if math.abs((plateMax or 0) - pm) > 0.5 then
                            hb:SetMinMaxValues(0, pm)
                        end
                        if math.abs((hb:GetValue() or 0) - pc) > 0.5 then
                            hb:SetValue(pc)
                        end
                    end
                end
            end
        end
    end
end)

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

local bridgesInstalled = false
installBridges = function()
    if bridgesInstalled then return end

    -- 1. GLOBAL OVERRIDE: catches everything that does global UnitHealth
    -- lookups at call time (Blizzard frames, EasyFrames, Kui, etc.).
    _G.UnitHealth    = bridgedHealth
    _G.UnitHealthMax = bridgedHealthMax

    -- 2. oUF / Luna direct-ref entries. The tag table grabs C-function
    -- references at file load and the global replace doesn't reach them.
    if oUF and oUF.Tags and oUF.Tags.Methods then
        local methods = oUF.Tags.Methods
        methods.curhp = bridgedHealth
        methods.maxhp = bridgedHealthMax
        if oUF.Tags.RefreshMethods then
            oUF.Tags:RefreshMethods("curhp")
            oUF.Tags:RefreshMethods("maxhp")
            oUF.Tags:RefreshMethods("perhp")
            oUF.Tags:RefreshMethods("missinghp")
        end
    end

    -- 3. pfUI fork that exposes its own tag table.
    if pfUI and pfUI.api and pfUI.api.tags then
        pfUI.api.tags["curhp"] = bridgedHealth
        pfUI.api.tags["maxhp"] = bridgedHealthMax
    end

    -- 4. Luna's oUF_TagsWithHeal defines its own UnitHasHealthData inside
    -- a private tag environment (`_ENV`) — it returns false for any
    -- player you're not grouped with (duel partners, BG/world PvP enemies),
    -- which forces smarthealth into the "X%" branch and hides the real
    -- numbers our bridge produces. Reach into that env via getfenv on a
    -- compiled tag and override it. _PROXY and _ENV are the same table,
    -- so the patch lands on every tag that shares the env.
    --
    -- NB: Luna's oUF is namespace-private (`LUF.oUF`, not `_G.oUF`); the
    -- TagsWithHeal table lives at `LUF.oUF.TagsWithHeal`. Fall back to a
    -- bare `oUF` global for other oUF forks that do expose it.
    local lunaOUF = (LUF and LUF.oUF) or oUF
    if lunaOUF and lunaOUF.TagsWithHeal and lunaOUF.TagsWithHeal.Methods then
        local probe = lunaOUF.TagsWithHeal.Methods.smarthealth  -- force lazy compile
        if type(probe) == "function" then
            local env = getfenv(probe)
            if type(env) == "table" then
                env.UnitHasHealthData = function() return true end
            end
        end
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
