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
- carry a request ID when it changes something. Sending the same ID again, to any node, must change nothing more.

A point is a version ID, a branch(its newest version) or branch@mark.

Every change answers where its request is: Written(its version), Conflicted(a merge or a resolve after which resources still clash), Pending(its owner group has not voted yet), Stale(its owners cannot take it at the newest version any more), Refused(it, or its branch, is contradicted) or NotSeen.

#### Read
- `try-get status` - what is mounted, who is connected and which branches this node owns.
- `try-get branches` - every branch, with its owner group and newest version.
- `try-get log <name> --branch <branch>` - the versions of a resource, with author and time.
- `try-get content <name> [point]` - the content of a resource at a point.
- `try-get diff <name> <a> <b>` - what changed, part by part, as the format of the resource reads it.
- `try-get affects <branch>` - the changes on other branches, not in this one yet, to anything this branch uses: its own resources, and what they import, at any depth.
- `try-get impact <point>` - what the changes up to this point touch on the branches that do not have them yet.
- `try-get answer <request-id>` - where a change that timed out is.
- `try-get conflict <merge>` - the resources that still clash after a merge.
- `try-get changes <topic> [--since X]` - the events of a topic as one answer(polling), and what to pass as --since next time.

#### Change
- `try-write <name> --branch <branch> --base <version>` - saves new content(bytes, a URI or an old version). The owner group refuses it as Stale when the resource changed since the base.
- `try-set-branch <branch> --to <point>` - makes the branch at that point or, when it exists, records a new version where the whole branch, submodules included, equals that point. History is kept.
- `try-create mark <branch> <name> -m <message>` - names the current point of a branch.
- `try-merge <point> into <branch>` - merges resource by resource, each in its own format. Conflicted stores the conflict.
- `try-resolve <conflict> <name> <content>` - settles one resource of a stored conflict.
- `try-mount <uri> [settings] --branch <name>` - ties a resource to a branch, and fills it when it is empty. The resource's kind reads and checks the settings(for kinds with paths, globs). On a mounted resource, it changes its settings or its branch(a checkout). A second mount of the same space on another branch is a worktree. Answers Mounted, Partial(names the submodules that could not be fetched), Unsupported(the kind does not support a setting) or Refused.
- `try-unmount <uri>` - stops versioning it. Answers Unmounted or NotMounted.

#### Formats
Each resource is read in the format of its path, and every format has its own diff and merge. Lines are the default; content that is not text is one whole part. A format can hold another inside it(CSS and JavaScript inside HTML, code inside Markdown), to any depth: its parts merge in their own formats. A language also reads what a resource imports, with the conditions and the alias of each import; affects and impact follow those imports. For every format, a diff applied to the old content gives the new one, and a merge takes the one change when only one side changed, or when both made the same change.

#### Nodes
- `try-set-owner <branch> <group>` - sets the owner group of a branch.
- `try-set-group <group> <member>...` - makes the group or, when it exists, replaces its members. A member is a node or a group.
- `try-sync <node>` - swaps history with another node: each sends what the other lacks. Answers Synced, Partial or Refused.
  Nodes that took in the same entries hold the same state, in any order and any number of times. A version that a node answered Written stays so after a sync that contradicts nothing it holds. A sync may leave groups that contain one another; the groups on such a cycle are a notice until a `try-set-group` settles them.

#### Connection
- `try-open <node-uri> --writer <writer>` - connects to a node as a writer. Answers Opened.
- `try-close` - ends the connection, or a subscription.

#### Live
- `try-subscribe <topic> [--since X]` - keeps sending the events of a topic: changes elsewhere that affect a branch, new conflicts, new versions, and groups that a sync left on a cycle.

#### The node itself
- `try-start-or-resume` - runs the node. Answers Busy when another node holds the store.
- `try-stop [--force]` - stops it. Without force, it refuses while mounts are active or other writers are connected.

#### Submodules
A submodule's own Vend Node must not be assumed to be local.
- The parent holds, for each child, a submodule resource with the space, the branch and the version of the child. Never a node address: any node that has that version can serve it.
- A child is mounted like any other resource, and its branch has its own owner group.
- A merge of two versions of a submodule takes the newer one when one came from the other; else it is a conflict.
- `try-mount` and `try-set-branch` fetch each child from whoever has it. When none can be reached, they answer Partial.
