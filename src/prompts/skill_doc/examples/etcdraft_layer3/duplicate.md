# Action: Duplicate

**Module**: Network

**Trigger**: Non-deterministic (spec level)

**Parameters**:
- `m`: message from messages set

**Control Flow**:
```
1. Select message m from messages
2. Add copy of m to messages:
   messages' = messages ∪ {m}
```

**Variable Changes**:
- `messages`: copy of m added
