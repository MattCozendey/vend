# TODO

Delete each item when it is done.

## Implement

- `src/conditions`: `Cond.sat`, `Cond.canon`.
- `src/history`: `Ids.is_eq`, `History.commit`, `History.join`.
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
  - No fsync after a write; a temp file left by a crash is never removed; files over 4 GiB (`File.size` is `U32`).

## Prove

Every law stated but not proven:

- `src/shared.bend`: `name_read_after_show`, `name_show_after_read`.
- `src/views/shared.bend` instances:
  - `src/views/text`: `Text.lossless`, `Text.join_after_lines`, `Text.same_equivalence`, `Text.patches`,
    `Text.diffs_nothing`, `Text.merges`.
  - `src/views/bend`: `Bend.lossless`, `Bend.keys_distinct`, `Bend.same_equivalence`, `Bend.patches`,
    `Bend.diffs_nothing`, `Bend.merges`.
- `src/store`: `node_is_eq`, `read_after_write`, `write_root`, `write_keeps`, `edit_root`, `read_after_edit`,
  `edit_keeps`, `write_collides`, `edit_collides`, `diff_applies`, `diff_answers`.
- `src/endpoints/spec.bend`: the 12 stream laws.
- `src/conditions`: `sat_holds`, `sat_unsat`, `canon_same`, `canon_unique`.
- `src/history`: `commit_refused`, `commit_node`, `commit_head`, `commit_keeps`, `commit_frames`, `join_keeps`,
  `join_adds_nothing`, `join_commutes`, `join_associates`, `join_idempotent`.
- `src/graph`: `affected_exact`.
- `src/endpoints/file`: `name_needs_resource`, `absent_only_when_known`, `read_only_files`,
  `non_resource_cannot_tell`, `temp_is_temp`, `absence_holds_only_known`, `notices_are_hints`.

## Strengthen

- `src/glob`: prove the path-validity automaton equals `Spec.is_path`, so that `Absent` also covers globs whose only
  shared strings are invalid paths (today: `Unknown`, for example `a/**` and `a/`).
