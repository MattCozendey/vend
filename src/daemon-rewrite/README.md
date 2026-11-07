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
