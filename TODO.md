# TODO

Delete each item when it is done.

## Implement

- `src/conditions` (BDDs): choose the atom order from the formula (atoms that appear together placed next to each
  other), or reorder while building: with name order, some formulas blow up (measured: 18.9 s for 20 atoms in a bad
  order, about 0 s in a good one). `Cond.canon` returns a tree, so a BDD that shares subgraphs comes back
  exponentially larger: if it becomes hot, keep the BDD itself in the graph, or give `Cond` a shared form. Its memo
  lookups go through `Table`, so they speed up with the faster `Table` inside.
- `src/history`: `History.join`.
- `src/views/bend`: after a merge, run the checker; report "merged, but the proofs fail" as its own outcome. With
  `src/impact`, this is the guarantee: no law statement changed and the merged result checks, so every law holds.
- `src/impact`: prune the radius by condition (`via` edges whose condition cannot hold under a query) with
  `Cond.sat`; today conditions are only reported.
- `src/store`: tree-aware `Tree.edit` (re-chunk only near the edit) and `Tree.diff` (skip shared subtrees). The first versions read and write everything.
- `src/endpoints/file`:
  - Symlinks: a link is its own resource whose content is its target (agreed design). Needs a readlink effect; today a
    link is `Unreachable`.
  - Linux (inotify) and macOS code: never compiled or run (written on Windows). macOS watching: not written yet.
  - JS lane watches by polling (the JS runtime never yields to Node's event loop): cost grows with the tree, and a
    same-size change within one clock tick is missed.
  - Debounce: a quiet window before fetching, so a truncate-then-write does not record the empty state.
  - Retry a transient Windows sharing violation during a fetch instead of reporting `Unreachable`.
  - A temp file left by a crash is never removed; files over 4 GiB (`File.size` is `U32`).
  - The JS lane locks the journal with a pid file (no flock there), so two loops that start at the same moment can
    both take it.
  - File URIs: percent-encoded characters are not decoded yet (a `%` is taken as itself).
- `src/shared.bend`: a faster Table inside (e.g. Base Map), proving the same three laws.
- `src/graph`: references across spaces (a reference with a scheme or an authority) through mounts; today unresolved.
- The daemon (`src/daemon`; built: one per user and machine, all mounts, started only by
  `bend-ver start-or-resume`, the down message, `status`, `mount`, `unmount`, guarded `daemon stop`, and the everyday
  commands `lines`, `log`, `show`, `diff`, `affects`, `impact`, `line new`, `write --expect`, `restore`, `mark`,
  `merge`). Left:
  - Next: the MCP server over stdio, a thin front like the CLI; it signs writes with the client name.
  - `affects` answers once; streaming it (what `clients` will count) is not built.
  - `log` lists versions in walk order from the heads, not in topological order.
  - `diff` takes versions (id prefixes, or a line for its head), not marks.
  - A merge into a line that is behind always makes a merge node (no fast-forward); a resource with several heads on
    either side clashes.
  - Decisions you may revisit: `write` reads its bytes from `--from <file>` (Base has no effect that reads standard
    input); a write without `BEND_VER_AGENT` is signed `unnamed`; a merge is all-or-nothing (one clash and no resource
    moves, so a line never holds half of a merge whose resources may need each other); `start-or-resume` runs in the
    foreground (a detached start needs a new foreign effect); the door is TCP on 127.0.0.1 with a random 128-bit token
    in the file `daemon` of the data folder (Unix sockets or named pipes need foreign code). On Windows the data folder
    is per user; on Linux and macOS Base cannot set file modes, so the `daemon` file gets the default mode (often
    readable by other users): setting it to 0600 needs foreign code.
  - A slow client holds the acceptor up to 2 seconds per read (one connection at a time).
  - A mount that fails at start (its root gone) is reported and skipped; it stays in the mounts file.
  - Mounting at run time primes the streams from the line the daemon holds; the daemon restores every line from the
    journal at start.
- `src/journal`: compaction (a snapshot of the store, history and lines, then a fresh log), so start-up does not
  replay everything and the journal stays below 4 GiB (it is read whole with `File.size`, a `U32`).
- `src/endpoints/file`: on POSIX, a rename is durable only after its directory is synced; sync the directory after
  the rename of a Put and of a journal cut.

## Prove

Every law stated but not proven. `Text.same_equivalence` needs `String.eq` symmetry and transitivity (reflexivity
and soundness are proven in `src/shared.bend`).

- `src/shared.bend`: `uri_read_after_show`, `uri_show_after_read`, `name_read_after_show`, `name_show_after_read`.
- `src/views/shared.bend` instances:
  - `src/views/text`: `Text.lossless`, `Text.same_equivalence`, `Text.patches`, `Text.diffs_nothing`,
    `Text.merges`.
  - `src/views/bend`: `Bend.lossless`, `Bend.keys_distinct`, `Bend.same_equivalence`, `Bend.patches`,
    `Bend.diffs_nothing`, `Bend.merges`, `refs_local`, `refs_imported`.
- `src/store`: `node_is_eq`, `read_after_write`, `write_root`, `write_keeps`, `edit_root`, `read_after_edit`,
  `edit_keeps`, `write_collides`, `edit_collides`, `diff_applies`, `diff_answers`.
- `src/conditions`: `sat_holds`, `sat_unsat`, `canon_same`, `canon_unique`.
- `src/history`: `node_encode_injective`, `add_refused`, `add_node`, `add_collides`, `add_idempotent`, `add_tips`,
  `new_ok`, `add_ok`, `join_keeps`, `join_adds_nothing`, `join_commutes`, `join_associates`, `join_idempotent`.
- `src/lines`: `advance_head`, `advance_frames`, `advance_descends`, `seen_caught_up`, `seen_frames`.
- `src/graph`: `affected_exact`.
- `src/core`: `noticed_follows_stream`, `records_each_version`, `fetched_reads_back`, `recorded_heads_line`,
  `write_accepted`, `write_authored`, `nested_untracked`, `step_keeps_history`, `replay_matches`, `restored_quiet`.
- `src/daemon`: `step_is_core`, `step_frames`, `step_frames_lines`, `unmount_drops`, `unmount_frames`,
  `request_decode_after_encode`, `response_decode_after_encode`, `token_checked`, `stop_guarded`, `stop_forced`,
  `mount_once`, `entries_decode_after_encode`, `replay_nil`, `replay_con`, `apply_saw`, `apply_marked`, `mark_fixed`,
  `apply_forked`, `apply_forked_mark`, `reads_record_nothing`, `write_stale`, `write_kept`, `merge_all_or_nothing`,
  `affects_sees`.
- `src/cli`: `parse_after_show` (restated for `mount`; its old proof covered `watch`, which is gone),
  `ask_passes_words`.
- `src/journal`: `read_after_encode`, `read_torn_tail`.
- `src/impact`: `classify_unchanged`, `classify_added`, `classify_removed`, `classify_statement`,
  `classify_proof_only`, `classify_covered`, `radius_has_changed`, `radius_closed`, `radius_minimal`,
  `layers_cover`.
- `src/endpoints/file`: `temp_is_temp`.

## Strengthen

- `src/glob`: prove the path-validity automaton equals `Spec.is_path`, so that `Absent` also covers globs whose only
  shared strings are invalid paths (today: `Unknown`, for example `a/**` and `a/`).
