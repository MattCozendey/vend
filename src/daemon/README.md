## RULES(S)
1 - IF YOU ARE AN AGENT, ONLY TOUCH THIS WITH EXPRESS PERMISSION AND ONLY ON THE AGENT-DESIGNATED SECTION UNLESS TOLD OTHERWISE. EVERYTHING ELSE IS HUMAN-WRITEN.

2 - This implementation must be independent from the outside code with exceptions:
2.1 - Glob. It's proven so it's fine.
2.2 - src/shared.bend | src/shared/*.bend

3 - This must not contain technical details(at most in the agent-designated section) and even when it does the main intention is imperative.

## GLOSSARY

### Vend Node
A Vend Node is program that can run anywhere which records versions of resources into branches and histories, sometimes giving semantic data for types of resources it knows how to decode(e.g responding whether a function is used anywhere in a Bend program). It talks bidirectionally with all consumers(those being writers and other Vend Nodes) and all resources(files, servers). Both sides must retry with exponential backoff, jitter and circuit breakers(and drop repeated by message ID).
Each branch has one owner group at a time(usually a single node). A member of a group is a node or another group; but no group can contain itself even indirectly. AN AGENT WROTE THIS: a change made on a node still cannot make a group contain itself, but a sync can. When two nodes change groups before they meet, the members each keeps may contain one another. The sync takes them anyway (see try-sync), and the groups on that cycle share their members until a try-set-group settles them. REVIEW LATER The group can change(by, for example, moving the branch to another node) and the owner group must refuse stale writes. Other nodes follow the branch with eventual consistency. When the owner group cannot be reached, writers keep wroing and their changes reach it later.
Each resource type(for example, file://) must have its own way of detecting changes, tuning retries on failures and optimize. For example, local files may use copy-on-write clones where the system supports it(normal copy else). A type may also limit possibilities(writing straight to disk may be detected but not refused).

we won't use file. We will use file-glob(our own URI-like scheme. no windows-nonsense. Always "/" and case sensitive)

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
- `try-get log <name> --branch <branch>` - the versions of a resource, with author and time.
- `try-get content <name> [point]` - the content of a resource at a point.
- `try-get diff <name> <a> <b>` - what changed, item by item for types the node knows how to decode.
- `try-get affects <branch>` - changes elsewhere that touch what this branch uses.
- `try-get impact <point>` - what this branch's changes touch elsewhere.
- `try-get outcome <request-id>` - whether a change that timed out happened.
- `try-get changes <topic> [--since X]` - the events of a topic as one answer(polling).

#### Change
- `try-write <name> --branch <branch> --base <version>` - saves new content(bytes, a URI or an old version). Answers Written, Pending(owner group not reached), Stale or Refused.
- `try-set-branch <branch> --to <point>` - makes the branch at that point or, when it exists, records a new version where the whole branch, submodules included, equals that point. History is kept. Answers Created, Restored, Pending, Partial(names the missing submodules), Stale or Refused.
- `try-create mark <branch> <name> -m <message>` - names the current point of a branch. Answers Marked, NameTaken or Refused.
- `try-merge <point> into <branch>` - merges item by item. Answers Merged, Conflicted(the conflict is stored), Stale or Refused.
- `try-resolve <conflict> <name> <content>` - settles one resource of a stored conflict. Answers Resolved(no resource clashes any more), Left(the resources that still clash), Stale or Refused.
- `try-mount <uri> [settings] --branch <name>` - ties a resource to a branch, and fills it when it is empty. The resource's kind reads and checks the settings(for kinds with paths, globs). On a mounted resource, it changes its settings or its branch(a checkout). A second mount of the same space on another branch is a worktree. Answers Mounted, Partial, Unsupported(the kind does not support a setting) or Refused.
- `try-unmount <uri>` - stops versioning it. Answers Unmounted or NotMounted.

#### Nodes
- `try-set-owner <branch> <group>` - sets the owner group of a branch. Answers Set, NoMajority or Refused.
- `try-set-group <group> <member>...` - makes the group or, when it exists, replaces its members. A member is a node or a group. Answers Set, Cycle(the group would contain itself), NoMajority or Refused.
- `try-sync <node> [--since X]` - swaps history with another node. Answers Synced, Partial or Refused.
  For each group, both nodes keep the members with the larger stamp(the newer set, and on a tie the larger member list), so they end with the same groups. A sync takes those members even when groups then contain one another: refusing them would search every group on every sync, and the nodes could still disagree. The groups on such a cycle share their members until a `try-set-group` settles them.

#### Connection
- `try-open <node-uri> --writer <writer>` - connects to a node as a writer. Answers Opened.
- `try-close` - ends the connection, or a subscription.

#### Live
- `try-subscribe <topic> [--since X]` - keeps sending the events of a topic: changes that affect you, new conflicts, new versions, groups that a sync left on a cycle and the node's questions to you. Answers questions with the matching command(for example, `try-resolve`).

#### The node itself
- `try-start-or-resume` - runs the node.
- `try-stop [--force]` - stops it.

#### Submodules
A submodule's own Vend Node must not be assumed to be local.
- The parent records, on each of its versions, the space, branch and version of each child. Never a node address: any node that has that version can serve it.
- A child is mounted like any other resource, and its branch has its own owner group.
- `try-mount` and `try-set-branch` fetch each child from whoever has it. When none can be reached, they answer Partial.
