# Task: Write a TLA+ Specification

Write a TLA+ specification that models the following system:

- **System**: ${TARGET_NAME}
- **Language**: ${TARGET_LANG}
- **Algorithm**: ${TARGET_REFERENCE}
- **Source Code**: ${REPO_DIR}

## Requirements

1. Read the system's source code to understand its behavior.
2. Write a TLA+ specification (`base.tla`) that models the system's core state transitions.
3. Write a TLC configuration file (`base.cfg`) that defines constants and invariants.
4. Write a model checking wrapper (`MC.tla` + `MC.cfg`) with appropriate constants
   for bounded model checking.

## Output

Write files to: `${SPEC_DIR}/`

- `base.tla` — Main specification
- `base.cfg` — Base configuration
- `MC.tla` — Model checking wrapper
- `MC.cfg` — Model checking configuration

## Validation

After writing the spec:

1. Check syntax by running SANY:
   `java -cp ${TLA2TOOLS_JAR} tla2sany.SANY ${SPEC_DIR}/MC.tla`

2. If syntax errors occur, fix them and re-check (up to 3 attempts).

3. If syntax passes, run TLC briefly to check for runtime errors:
   `java -cp ${TLA2TOOLS_JAR}:${COMMUNITY_JAR} tlc2.TLC ${SPEC_DIR}/MC.tla -config ${SPEC_DIR}/MC.cfg -workers auto -deadlock`

4. If runtime errors occur, fix them and re-run (up to 3 attempts).
