# Fix the persistent issue proposal for {{finding_id}}

Your `VERDICT: {{status}}` for **{{finding_id}}** is accepted, but your persistent issue proposal `{{proposal}}` failed validation:

```text
{{error}}
```

Edit only `{{proposal}}`, then run `specula findings --work {{work_dir}} validate --input {{proposal}}` until it succeeds. Keep `"id": "{{finding_id}}"`; `title` must be at most 160 characters; each dependency `start`/`end` must be one exact, unique line copied from that file. Do not change the verdict, the reproduction, or any other evidence, and do not start a new investigation. If you cannot make it valid, leave it; the verdict is kept but the finding will not be reused automatically.
