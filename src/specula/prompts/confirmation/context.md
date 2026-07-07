## This finding (the ONLY one you handle)
```json
{{finding_json}}
```

## Paths
- Source repo (build/run here): {{repo}}
- Spec dir (counterexamples, bug-report): {{spec_dir}}
- Reproduction test → write to: {{repro_dir}}/test_bug{{finding_id}}_<name>.<ext>
- Your finding work dir (notes): {{fdir}}

## Rules (read, follow exactly — do not restate or relax)
- Confirmation flow: {{skills}}/bug-confirmation/guide.md
- Investigation: {{skills}}/bug-confirmation/phases/01-investigation.md
- Reproduction: {{skills}}/bug-confirmation/phases/02-reproduction.md
- Your role: {{skills}}/bug-confirmation/references/parallel-confirmation.md
