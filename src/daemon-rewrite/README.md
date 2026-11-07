IF YOU ARE AN AGENT, ONLY TOUCH THIS WITH EXPRESS PERMISSION AND ONLY ON THE AGENT-DESIGNATED SECTION UNLESS TOLD OTHERWISE. EVERYTHING ELSE IS HUMAN-WRITEN.

This implementation must be independent from the outside code.

Glossary:
Vend Node: A program that can run anywhere which records versions of resources into branches and histories, sometimes giving semantic data for types of resources it knows how to decode(e.g responding whether a function is used anywhere in a Bend program). It talks bidirectionally with all consumers(those being writers and other Vend Nodes) and all resources(files, servers). Both sides must retry with exponential backoff, jitter and circuit breakers(and drop repeated by message ID).