# Action: Drop

**Module**: Network

**Trigger**: Non-deterministic (spec level)

**Parameters**:
- `m`: message from messages set

**Control Flow**:
```
1. Select message m from messages
2. Remove m from messages:
   messages' = messages \ {m}
3. Do not deliver (message lost)
```

**Variable Changes**:
- `messages`: m removed
