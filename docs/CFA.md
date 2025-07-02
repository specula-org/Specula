# TLAPLUS CFA

This project is a **Control Flow Analysis (CFA) framework** for TLA+.
Although it is currently a submodule of the Specula project, 
    its usage does not depend on other Specula modules and can be used independently (e.g., for automatically adding `UNCHANGED` statements). This document focuses on introducing the features used by Specula.

In the Specula project, the framework performs control flow analysis on TLA+ specifications 
    to transform *translated specs* (raw specs that were directly translated from source code) 
    into specs that can be accepted by TLC. 

The algorithms mainly solve three problems:

1. **Single Assignment Constraint**: In atomic actions, a variable can be assigned at most once.
2. **UNCHANGED Requirement**: For variables that are not modified in atomic actions, explicit `UNCHANGED <<var>>` statements must be provided.
3. **State Annotation**: Variables that use modified states in atomic actions need to be explicitly annotated (using `'`).

## Definitions

### Translated Spec

**Translated Spec** is obtained by using LLMs to translate source code into the TLA+ format on a statement-by-statement basis. 
A translated spec strictly describe the logic of the code and the control flow of the statements. 
However, due to multiple assignments and complex calling relationships in source code, 
    the translated spec is often not accepted by TLC.

One may be curious why not not directly use LLMs to generate a TLA+ specification instead of doing translation first? 
In our experience, LLMs suffer from overfitting and over-imitation of well-known specifications;
so, directly generating the TLA spec often misses or oversimplifies logic, 
    making it impossible to precisely describe the source code.

For example, in the following translated spec, the `electionElapsed` variable is modified twice, 
    violating the definition of atomic actions in TLA+:

```tla
tickHeartbeat(s) ==
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = electionElapsed[s] + 1]
    /\ IF electionElapsed'[s] >= 3
       THEN /\ electionElapsed' = [electionElapsed' EXCEPT ![s] = 0]
            /\ ...
       ELSE /\ UNCHANGED <<messages, leadTransferee>>
    /\ ...
```

### Control Flow in TLA+

Our CFA framework treats each statement as a unit code block, recording the calling and transfer relationships between code blocks, and analyzing all variables that may be assigned when reaching each code block.

For the following TLA+ code:

```tla
IF a < b 
    THEN a' = a + 1
    ELSE b' = b + 1 
```

The following control flow is obtained:

<img src="./images/CFA_example.png" alt="Control Flow Example" width="300" />

## Control Flow Graph Construction

The control flow analysis framework mainly consists of **3 steps**: 
**Translated spec in TLA+ → CFG (Control Flow Graph) → CFA (Control Flow Analysis) → TLA+ spec**

### Compilation

First, we need to perform lexical analysis and syntax analysis 
    on the translated spec (or in fact any input spec) to obtain an Abstract Syntax Tree (AST).

So, why not use `tla_sany`, the lexical and syntax analyzer that comes with TLC?
The reason is that rules in `tla_sany` are overly complex and convoluted.
If modifications are needed later, rewriting becomes extremely complex. 
Moreover, we find that its syntax tree format is very difficult to use 
    for generating specs.

### Tools

We use **ANTLR** as the parser generation and visualization tool, which has two advantages:
1. **Code insertion capability**: Allows inserting code in parsing rules to provide more complex logic
2. **Visualization interface**: Provides visual debugging capabilities

### Lexical and Syntax Rules

The rules are mainly referenced from Lamport's **"Specifying Systems"**.

<img src="./images/tla_grammar.png" alt="TLA+ Grammar" width="600" />

**Challenges addressed:**
- **Ambiguity issues**: Modified the original rules to resolve ambiguities. See [TLAPlusLexer.g4](../tools/cfa/src/main/java/grammar/TLAPlusLexer.g4) and [TLAPlusParser.g4](../tools/cfa/src/main/java/grammar/TLAPlusParser.g4)
- **Indentation sensitivity**: Borrowed techniques from Python Documentation's ANTLR4-based Python syntax analyzer. By rewriting the CommonTokenStream after lexical analysis to match indentation-sensitive rules. See [TLAPlusLexerBase.java](../tools/cfa/src/main/java/parser/TLAPlusLexerBase.java)

### Control Flow Graph (CFG) Construction

After obtaining the AST, we establish code blocks with statements as units, 
    building transfer relationships and calling relationships between code blocks 
    by traversing the code blocks. 
See [CFGBuilderVisitor.java](../tools/cfa/src/main/java/CFG/CFGBuilderVisitor.java)

## Control Flow Analysis (CFA)

Our CFA transforms the CFG through three main algorithms to make it conform to TLA+'s atomic action semantics. 
The implementation is located in `tools/cfa/src/main/java/CFG`.

### 1. Static Analysis Preprocessing

First, CFA performs static analysis on the input spec 
    to identify potential problems that violate TLA+ atomicity requirements.

- **Variable analysis**: Analyzing variable modification situations and dependency relationships
- **Problem identification**: Marking non-atomic operation segments that require subsequent transformation  
- **Information gathering**: Providing necessary data flow and function call information for subsequent algorithms

### Process Cutting Algorithm

This is the core transformation algorithm that resolves contradictions 
    between imperative control flow and TLA+'s atomic state transition requirements.

**Problem**: A single function in high-level programming languages may contain multiple assignments to the same variable or multiple logical steps, while in TLA+ each step must be modeled as an independent atomic action.

**Solution**: Systematically decomposing complex actions in the input spec:
- **Auxiliary variables**: Introducing auxiliary state variables (e.g., program counter `pc`, call stack `stack`, etc.) to manage execution context
- **Action splitting**: Automatically splitting single large actions into multiple TLA+-compatible atomic action sequences

**Function Call Handling**: The algorithm can automatically distinguish between:
- **Simple function calls**: Directly inlined into the caller's action sequence
- **Complex function calls**: Transformed into independent atomic action sequences, with execution flow managed through auxiliary variables

**Example**:

<img src="./images/pc_example.png" alt="Process Cutting Example" width="800" />

### UNCHANGED Convergence Algorithm

Solves the problem that TLA+ requires all variables in each atomic action to be explicitly handled see (see [tlaplus-677](https://github.com/tlaplus/tlaplus/issues/677)).

**Objective**: Automatically insert `UNCHANGED` clauses for variables not modified in actions.

**Strategy**:
- **Confluence analysis**: Analyze control flow confluence points (where multiple execution paths merge)
- **State analysis**: Analyze variable states at these key points
- **Selective insertion**: Add `UNCHANGED` clauses only when necessary to avoid over-constraining the model

**Example**:

<img src="./images/uc_example.png" alt="UNCHANGED Convergence Example" width="600" />

### Variable State Update Algorithm

Handles the syntax requirements for current state and next state variables in TLA+.

**Problem**: Translated Spec reflects an imperative memory state model, while TLA+ needs to clearly distinguish between a variable's current state value and next state value.

**Solution**: Refactor expressions to conform to TLA+'s state transition syntax conventions, ensuring all next-state assignments are correctly annotated (using the `'` symbol).

**Example**:

<img src="./images/ud_example.png" alt="Variable Update Example" width="500" />

## TLA+ Specification Generation

The final stage serializes the transformed and validated CFG into a structurally correct TLA+ specification:

### CFG Printer

Uses a dedicated **TLA+ CFG Printer** with a recursive strategy to convert CFG into TLA+ textual representation:

- **Confluence identification**: Identify control flow confluence points
- **Expression generation**: Recursively generate corresponding TLA+ action expressions  
- **Specification composition**: Combine to generate complete specifications

Implementation is located in `tools/cfa/src/main/java/printer`.

### Output Specification

The final output specification should have the following characteristics.

- **Structural correctness**: Structurally correct and formally complete
- **Semantic compliance**: Conforms to TLA+ atomic action semantics
- **Logical fidelity**: Faithfully models the logic of the original imperative code
- **Verification ready**: Can be directly verified by the TLC model checker
