# Terminal panic observation boundary

One V01 negative case has nondeterministic partial raft.msgs after a configuration-triggered broadcast panic. V01 ProgressTracker.Visit iterates an unordered Go map, whereas the TLA helper selects one order. The native status and all other compared fields agree after control-flow repair. V02/V03 Visit sorts IDs.

The partial volatile output queue is not delivered: raft.send only buffers messages; the atomic core call panics before the caller can collect a subsequent Ready. The reference marks the node fatal and Live disables Ready/Publish; restart discards the volatile queue. Under this terminal-panic contract, the partial internal messages are outside the observable post-state. The adapters retain raw evidence and compare the rest of the state. This projection is not valid for a language/runtime that permits recovery and continued use of the same object after the exception; regenerated adapters must specify their own error boundary.

Do not label a differing partial queue after this panic a confirmed model or implementation bug. Do not ignore messages on successful calls, returned errors, disabled calls, or before the action. The independent record comparison below projects only the post-panic state.messages when both engines report panic.
