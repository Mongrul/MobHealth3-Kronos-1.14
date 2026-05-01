# MobHealth3 — Kronos Edition

Real HP values for Kronos, the TrinityCore-based 1.12 private server,
when played through a modern WoW Classic Era client (Interface 11402).

---

## Features

- **Static NPC database** (`Data.lua`, ~10K entries) — known mobs report
  exact HP from frame one.
- **Combat-log accumulator** for players and unlisted NPCs. Damage and
  healing samples are correlated against percent changes to back out the
  real max HP.
- **Overkill, absorbs and overhealing are subtracted** from credited
  damage / heal amounts so PvP shield-users and the killing blow on each
  kill don't inflate the estimate.
- **Heal sampling.** `SPELL_HEAL` and `SPELL_PERIODIC_HEAL` events feed
  the same accumulator with reverse samples, roughly doubling the data
  rate in any fight where someone gets healed.
- **Signed-delta accumulator** discards samples where tracked HP
  movement disagrees in sign with the percent change (visibility gap),
  rather than corrupting the running ratio.
- **Player sanity filter.** Estimates outside `[level × 30, level × 130]`
  fall back to a class-based baseline (warrior 90/level, mage 55/level,
  etc.) — catches absorb-induced drift even on snapshots.
- **Persisted snapshots** in `MobHealth3SavedDB`. The second time you
  encounter a player or rare mob, the bridge returns real values
  immediately. Fresh accumulator data overrides stale snapshots once it
  builds past the divergence threshold (gear changes, level-ups, talent
  swaps).
- **O(1) name lookup.** A lazily-built name index replaces the original
  O(N) `pairs()` scan over Data.lua, making the addon viable in 80v80
  PvP where every visible enemy triggers DB lookups every frame.
- **Frame and nameplate sync** — keeps the default Blizzard target
  frame bar's range and value synced to bridged values so 2-box /
  cross-client scenarios don't leave the bar stuck. Same treatment for
  Blizzard nameplates via `C_NamePlate.GetNamePlates()`.
- **Self-target / pet / party / raid handling.** Indirect tokens like
  `target` are resolved via `UnitIsUnit` / `UnitInParty` so targeting
  yourself or a party member shows real HP straight from the server,
  not an estimator guess.

## Compatibility

**Server:** Kronos (TrinityCore 1.12). The threshold logic and
percentage assumption are specific to this server — would also fit any
other TrinityCore 1.12 server with the same proxy behavior.

**Client:** WoW Classic Era 1.14.x. TOC interface `11402`. Bump the TOC
if Blizzard moves the client.

**Bridged addons** (real HP values flow through automatically with no
configuration):

- **Default Blizzard frames** — TargetFrame, FocusFrame, nameplates.
- **EasyFrames** — text formats read `UnitHealth` directly; bar
  range/value kept in sync via OnUpdate.
- **Luna Unit Frames** (oUF + `oUF_TagsWithHeal`) — `smarthealth`,
  `smarthealthp`, `curhp`, `maxhp`, `perhp`, `missinghp` etc. all
  resolve through our bridge. The plugin's private `UnitHasHealthData`
  function is patched so duel partners and BG/world-PvP enemies don't
  get forced into the "X%" branch.
- **NeatPlates** (and themes / NeatPlatesHub) — calls `UnitHealth` via
  globals, picks up bridged values automatically. Configure a health
  text mode under `/np` → Text to display them.
- **ShadowedUnitFrames** — confirmed working via the global override.
- **pfUI** — receives the static DB at `pfUI.api.libmobhealth` and has
  its `pfUI.api.tags["curhp"]` / `["maxhp"]` patched to use the bridge.
- **Anything else that calls `UnitHealth` / `UnitHealthMax`** through
  globals (the bridge is installed at `_G`).

**Legacy API compatibility** — preserved from MobHealth / MobHealth2 so
older addons that probed for them keep working:

- `MobHealthDB[name..":"..level]` → `"max/100"` string.
- `MobHealth_GetTargetCurHP()` / `MobHealth_GetTargetMaxHP()` → numbers.
- `MobHealth_PPP(index)` → health-per-percent.
- A `MobHealthFrame` sniff frame so addons probing for MH/MH2/MI2 detect
  it.

## Installation

1. Close World of Warcraft.
2. Drop the `MobHealth/` folder into
   `World of Warcraft/_classic_era_/Interface/AddOns/`.
3. Launch the game; enable **MobHealth3 Kronos Edition** in the AddOns
   menu on the character select screen.
4. Log in. You'll see `MobHealth3: Kronos edition loaded.` in chat once
   the bridge installs at `PLAYER_LOGIN`.

## Usage

There's nothing to configure — the bridge installs automatically. Real
values appear immediately for any unit in the static DB; players and
unlisted NPCs converge after about 5% of HP has been damaged or healed
on them (after that, snapshots persist for instant accuracy on
re-engagement).

Slash commands:

- `/mh3` or `/mobhealth3` — prints accumulator state for the current
  target. Useful for diagnosing whether the estimator is building
  samples for a particular unit.

## How it works

1. **Friendly real units** (player, pet, party, raid, and any
   `target`/`mouseover` that resolves to one of them) → pass-through.
   Server already provides real values.
2. **Static DB hit** → return the cached max for that name (with level
   scaling if the DB entry is at a different level).
3. **Persisted snapshot** → if a previous session converged on an
   estimate for this name, use it as the starting point.
4. **Combat-log accumulator** → once `≥ 5%` of HP movement has been
   tracked this session with matching damage/heal samples, switch to
   the fresh estimate (and update the snapshot if it diverges by
   `> 5%`).
5. **Low-confidence fallback** → return the raw percentage with `max =
   100`. Other addons treat this as "live data not yet available."

The bridge replaces `_G.UnitHealth` / `_G.UnitHealthMax` once at
`PLAYER_LOGIN` and patches a handful of addons with private tag tables
(Luna's `oUF.TagsWithHeal`, pfUI). Combat-log capture uses
`COMBAT_LOG_EVENT_UNFILTERED` and `CombatLogGetCurrentEventInfo()` —
1.12-era `CHAT_MSG_COMBAT_*` parsing is gone.

## Limitations

- **Players and unlisted NPCs need ~5% of damage / healing observed**
  before the estimator switches from percent fallback to real values.
  Snapshots remove this delay on re-engagement.
- **Cross-client 2-boxing** can leave the bar's value stale because
  Blizzard's `UNIT_HEALTH` events don't always fire on the watching
  client. The OnUpdate loop refreshes the target frame and nameplate
  bars every 0.2s to compensate.
- **Mana / resource bars are not bridged.** Kronos uses the same
  percentage trick for power values for non-friendly units; the same
  approach would extend to those but isn't currently implemented.

## Acknowledgments

Maintained by **Mirasu of Kronos**.
