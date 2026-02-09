# Action: Receive

**Module**: Network

**Trigger**: Non-deterministic (spec level)

**Parameters**:
- `m`: message from messages set

**Control Flow**:
```
1. Select message m from messages
2. Remove m from messages:
   messages' = messages \ {m}
3. Deliver to destination:
   dest.Step(m)
```

**Variable Changes**:
- `messages`: m removed
- Destination state: updated by Step(m)
