# TODO

Delete each item when it is done.

## Implement

- `src/conditions`: `Cond.sat`, `Cond.canon`.
- `src/history`: `History.join`.
- `src/graph`: `Graph.affected`.
- `src/views/text`: `Text.diff`, `Text.patch`, `Text.merge`.
- `src/views/bend`: `Bend.decode`, `Bend.diff`, `Bend.patch`, `Bend.merge`.
- `src/views/bend`: after a merge, run the checker; report "merged, but the proofs fail" as its own outcome.
- `src/store`: tree-aware `Tree.edit` (re-chunk only near the edit) and `Tree.diff` (skip shared subtrees). The first versions read and write everything.
- `src/endpoints/file`:
  - Symlinks: a link is its own resource whose content is its target (agreed design). Needs a readlink effect; today a
    link is `Unreachable`.
  - Linux (inotify) and macOS code: never compiled or run (written on Windows). macOS watching: not written yet.
  - JS lane watches by polling (the JS runtime never yields to Node's event loop): cost grows with the tree, and a
    same-size change within one clock tick is missed.
  - Debounce: a quiet window before fetching, so a truncate-then-write does not record the empty state.
  - Retry a transient Windows sharing violation during a fetch instead of reporting `Unreachable`.
  - No fsync after a write; a temp file left by a crash is never removed; files over 4 GiB (`File.size` is `U32`).
  - File URIs: percent-encoded characters are not decoded yet (a `%` is taken as itself).
- `src/core`: more than one mount per loop, and a `--line` option in the CLI (today: one mount, line `main`).
- `src/graph`: references across spaces (a reference with a scheme or an authority) through mounts; today unresolved.

## Prove

Every law stated but not proven:

- `src/shared.bend`: `uri_read_after_show`, `uri_show_after_read`, `name_read_after_show`, `name_show_after_read`.
- `src/views/shared.bend` instances:
  - `src/views/text`: `Text.lossless`, `Text.join_after_lines`, `Text.same_equivalence`, `Text.patches`,
    `Text.diffs_nothing`, `Text.merges`.
  - `src/views/bend`: `Bend.lossless`, `Bend.keys_distinct`, `Bend.same_equivalence`, `Bend.patches`,
    `Bend.diffs_nothing`, `Bend.merges`.
- `src/store`: `node_is_eq`, `read_after_write`, `write_root`, `write_keeps`, `edit_root`, `read_after_edit`,
  `edit_keeps`, `write_collides`, `edit_collides`, `diff_applies`, `diff_answers`.
- `src/endpoints/spec.bend`: the 14 stream laws.
- `src/conditions`: `sat_holds`, `sat_unsat`, `canon_same`, `canon_unique`.
- `src/history`: `add_refused`, `add_node`, `add_keeps`, `add_idempotent`, `add_tips`, `add_frames`, `join_keeps`,
  `join_adds_nothing`, `join_commutes`, `join_associates`, `join_idempotent`.
- `src/lines`: `advance_refused`, `advance_head`, `advance_frames`, `advance_descends`.
- `src/graph`: `affected_exact`.
- `src/core`: `untracked_ignored`, `noticed_follows_stream`, `records_each_version`, `fetched_reads_back`,
  `recorded_heads_line`, `write_refused`, `write_accepted`, `move_remembered`, `nested_untracked`,
  `step_keeps_history`.
- `src/cli`: `parse_after_show`.
- `src/endpoints/file`: `resource_needs_path`, `absent_only_when_known`, `read_only_files`,
  `non_resource_cannot_tell`, `temp_is_temp`, `absence_holds_only_known`, `notices_are_hints`.

## Strengthen

- `src/glob`: prove the path-validity automaton equals `Spec.is_path`, so that `Absent` also covers globs whose only
  shared strings are invalid paths (today: `Unknown`, for example `a/**` and `a/`).
