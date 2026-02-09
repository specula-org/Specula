# Module: Network

## Responsibility

Model message delivery semantics. Abstract away real network details.

## Actions

### Receive

**Responsibility**: Deliver message to destination node

**Trigger**: Non-deterministic (any pending message can be delivered)

**Behavior**:
1. Pick message m from messages set
2. Remove m from messages (or keep for duplication)
3. Deliver to destination node's Step() function

**Code Reference**: (spec level, not in code)

---

### Drop

**Responsibility**: Lose a message

**Trigger**: Non-deterministic

**Behavior**:
1. Pick message m from messages set
2. Remove m from messages
3. Don't deliver

**Code Reference**: (spec level, not in code)

---

### Duplicate

**Responsibility**: Create copy of message

**Trigger**: Non-deterministic

**Behavior**:
1. Pick message m from messages set
2. Add copy of m to messages
3. (Original remains, now have two copies)

**Code Reference**: (spec level, not in code)

---

## Network Model

### Message Set Semantics

- Messages modeled as unordered set
- No FIFO guarantees
- Any message can be delivered at any time
- Messages can be lost (dropped)
- Messages can be duplicated

### Partition Modeling

Partition between node sets A and B:
- Drop all messages from A to B
- Drop all messages from B to A
- Modeled implicitly by Drop action

## Design Choices

| Aspect | Choice | Reason |
|--------|--------|--------|
| Ordering | Unordered set | Simplest, most general |
| Loss | Explicit Drop action | Tests failure handling |
| Duplication | Explicit Duplicate action | Tests idempotency |
| Delay | Implicit in non-determinism | No timing in spec |

## Message Lifecycle

```
Send(m) → messages' = messages ∪ {m}
Receive(m) → messages' = messages \ {m}, deliver m
Drop(m) → messages' = messages \ {m}
Duplicate(m) → messages' = messages ∪ {copy of m}
```
