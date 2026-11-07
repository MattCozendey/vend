## RULES(S)
1 - IF YOU ARE AN AGENT, ONLY TOUCH THIS WITH EXPRESS PERMISSION AND ONLY ON THE AGENT-DESIGNATED SECTION UNLESS TOLD OTHERWISE. EVERYTHING ELSE IS HUMAN-WRITEN.

2 - This implementation must be independent from the outside code.

3 - This must not contain technical details(at most in the agent-designated section) and even when it does the main intention is imperative.

## GLOSSARY

### Ven Node
A Vend Node is program that can run anywhere which records versions of resources into branches and histories, sometimes giving semantic data for types of resources it knows how to decode(e.g responding whether a function is used anywhere in a Bend program). It talks bidirectionally with all consumers(those being writers and other Vend Nodes) and all resources(files, servers). Both sides must retry with exponential backoff, jitter and circuit breakers(and drop repeated by message ID).
Each branch has one owner group at a time(usually a single node). A member of a group is a node or another group; but no group can contain itself even indirectly. The group can change(by, for example, moving the branch to another node) and the owner group must refuse stale writes. Other nodes follow the branch with eventual consistency. When the owner group cannot be reached, writers keep wroing and their changes reach it later.
Each resource type(for example, file://) must have its own way of detecting changes, tuning retries on failures and optimize. For example, local files may use copy-on-write clones where the system supports it(normal copy else). A type may also limit possibilities(writing straight to disk may be detected but not refused)

## Agents

### Public API
The CLI commands below expose the whole of what a Vend Node offers. Every other way to talk to a node(MCP, network, another node) must offer the same. We use the CLI here only because it is easier to read.

Every command must:
- start with try-, since the node may be anywhere. Any command may answer TimedOut or Unreachable(not repeated below).
- carry a request ID when it changes something. Sending the same ID again must change nothing more.
- answer with a position, for use with --since.

A point is a version ID, a branch(its newest version) or branch@mark.

#### Read
- `try-get status` - what is mounted, who is connected and which branches this node owns.
- `try-get branches` - every branch, with its owner group and newest version.
- `try-get log <name>` - the versions of a resource, with author and time.
- `try-get content <name> [point]` - the content of a resource at a point.
- `try-get diff <name> <a> <b>` - what changed, item by item for types the node knows how to decode.
- `try-get affects <branch>` - changes elsewhere that touch what this branch uses.
- `try-get impact <point>` - what this branch's changes touch elsewhere.
- `try-get outcome <request-id>` - whether a change that timed out happened.
- `try-get changes <topic> [--since X]` - the events of a topic as one answer(polling).

#### Change
- `try-write <name> --base <version>` - saves new content(bytes, a URI or an old version). Answers Written, Pending(owner group not reached), Stale or Refused.
- `try-restore <branch> --to <point>` - records a new version where the whole branch, submodules included, equals that point. History is kept. Answers Restored, Pending, Partial(names the missing submodules) or Stale.
- `try-create branch <name> --from <point>` - makes a branch. Answers Created or NameTaken.
- `try-create mark <branch> <name> -m <message>` - names the current point of a branch. Answers Marked or NameTaken.
- `try-merge <point> into <branch>` - merges item by item. Answers Merged, Conflicted(the conflict is stored) or Stale.
- `try-resolve <conflict> <choice>` - settles a stored conflict. Answers Resolved or Stale.
- `try-mount <uri> [globs] --branch <name>` - ties a resource to a branch, and fills it when it is empty. A second mount of the same space on another branch is a worktree. Answers Mounted, Partial or Refused.
- `try-unmount <uri>` - stops versioning it.

#### Nodes
- `try-change-owner <branch> <group>` - moves a branch to another owner group. Answers Changed, NoMajority or Refused.
- `try-sync <node> [--since X]` - swaps history with another node. Answers Synced, Partial or Refused.

#### Live
- `try-subscribe <topic> [--since X]` - keeps sending the events of a topic: changes that affect you, new conflicts, new versions and the node's questions to you. Answers questions with the matching command(for example, `try-resolve`).

#### The node itself
- `try-start-or-resume` - runs the node.
- `try-stop [--force]` - stops it.

#### Submodules
A submodule's own Vend Node must not be assumed to be local.
- The parent records, on each of its versions, the space, branch and version of each child. Never a node address: any node that has that version can serve it.
- A child is mounted like any other resource, and its branch has its own owner group.
- `try-mount` and `try-restore` fetch each child from whoever has it. When none can be reached, they answer Partial.
