# Chapter 4: Generate `Update.tla`

Build one update-focused model-checking view over the completed reference/MC suite. Do not duplicate changed implementation semantics.

## 1. Module Role

Prefer:

```tla
---- MODULE Update ----
EXTENDS MC
```

Use the exact module names and MC variable groups in the target suite. If the existing MC module cannot be extended cleanly, make the smallest target-specific adjustment while keeping reference behavior single-owned.

## 2. Affected Actions

Alias or wrap the MC forms of every directly changed reference Action:

```tla
AffectedActions ==
    \/ \E i \in Server : MCHandleVote(i)
    \/ \E i \in Server : MCApplyConfigChange(i)
```

Use MC wrappers when they own counters or framing state. Do not call a base Action directly and leave MC variables unconstrained. Do not copy the Action body into `Update.tla`.

## 3. Interaction Actions

Add concrete unchanged Actions that are important to the update Scenario because they:

- establish an affected Action's precondition;
- read, overwrite, persist, send, retry, cancel, or recover its result;
- cross a changed atomicity/fault boundary;
- expose a consumer-visible consequence.

Prefer concrete Actions for high-risk interactions that deserve deep schedule exploration.

## 4. Update-Visible State and Environment

Identify the variables necessary to state the update properties and interaction boundary. When relevant reference Actions are omitted from the concrete focused model, read `modular-verification.md` and define an evidence-based `EnvUpdate` summarizing their tolerated effects:

```tla
OpenUpdateNext ==
    \/ AffectedActions
    \/ InteractionActions
    \/ EnvUpdate
```

Define discharge obligations showing that omitted real context Actions satisfy `EnvUpdate`, with correct frame conditions. Do not use an unconstrained environment to make the local property vacuous.

## 5. Update-Specific Properties

Define:

- revised correctness properties such as `Inv_new`;
- properties introduced by the update;
- properties about changed/unchanged Action interaction;
- targeted structural or temporal properties justified by update Scenarios.

Every property must cite its Scenario and source/reference evidence. Later validation must check it against full `MCNext`; an open focused property additionally requires discharge checking.

## 6. Focused Specs and Configs

Provide separate entry points/configs for:

- update properties over full `MCNext`;
- concrete focused `AffectedActions \/ InteractionActions`;
- open focused behavior including `EnvUpdate` when used;
- discharge obligations for omitted context Actions;
- Scenario-specific BFS and simulation settings to be used in later validation.

At generation time, ensure each cfg names existing spec/property operators and that every update property is enabled somewhere. Do not run the later exhaustive/simulation campaign in this chapter.

## 7. Reverse Mapping

At each focus definition, point back to reference and source:

```tla
\* reference: base!HandleVote
\* code: src/path/file.ext:<line-range-or-symbol>
```

For assumption/setup/variable/helper changes represented only in reference, add a concise comment explaining how that change alters the selected Actions, environment, or properties.
