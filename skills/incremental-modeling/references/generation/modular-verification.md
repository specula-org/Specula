# Open Update Specs and Discharge Checking

Read this chapter when a focused `Update.tla` omits reference Actions that can affect update-visible state or changed Action enablement.

## Sources

- Murat Demirbas, [Composition and Modular Verification of TLA+ specs](https://muratbuffalo.blogspot.com/2026/08/composition-and-modular-verification-of.html).
- [Producer/consumer TLA+ and TLAPS artifact](https://github.com/muratdem/modularTLA/tree/main/producer-consumer-modular).

## Why It Matters Here

Do not conjoin `Update.tla` as a second closed behavior model with the reference. Closed specs that both write shared state can overconstrain each other. In Incremental Specula, reference Actions remain the sole behavior definitions; `Update.tla` selects them and optionally gives omitted context an explicit environment/rely action.

## Open Update Pattern

```tla
OpenUpdateNext ==
    \/ AffectedActions
    \/ InteractionActions
    \/ EnvUpdate
```

- Keep high-risk interactions concrete.
- Let `EnvUpdate` describe only the remaining context effects relevant to update properties.
- State explicitly which update-visible variables the environment may change and which it must preserve.
- Avoid both extremes: an environment so strong that it excludes legal context, or so weak that properties become meaningless.

## Discharge Obligations

Check that every omitted real context Action is accepted by the rely:

```tla
DischargeContext ==
    []((OmittedContextActions /\ Frame) => EnvUpdate)
```

Include frame conditions for private/MC variables. If discharge fails, investigate whether:

- the context Action should be included concretely;
- `EnvUpdate` is too strong or otherwise wrong;
- a type-correct but unreachable state needs an already-established local invariant;
- the reference model or update property is incorrect.

Do not invent an assumption solely to silence a discharge counterexample.

## Later Validation Contract

The generation phase only creates these operators/configs. Later validation must run:

1. update properties over full `MCNext`;
2. concrete focused checking;
3. open focused checking;
4. discharge checking;
5. full checks on the stabilized repaired suite under the [model-checking repair loop and final-check rules](../model-checking/01-update-focused-checking.md#counterexamples-and-back-edges), not after each individual edit.

Focused checking never replaces full reference validation. When `EnvUpdate` is used, discharge is additional, not an alternative to full `MCNext`.

## Chaos Universe and TLAPS

A chaos/type universe can check single-step implications over all type-correct state pairs without constructing full reachability. Expect unreachable counterexamples; strengthen only with local invariants already established in the complete reference.

Use TLC first. Consider writing discharge lemmas and checking them with TLAPS only after real cases show that finite bounds or state-space cost limit the TLC checks. Safety action relies fit this pattern; do not assume it directly handles liveness relies.

Do not decompose the entire existing reference into open components. This method is a focused completeness guard around `Update.tla`, not a replacement architecture for Specula.
