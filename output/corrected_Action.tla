```json
{

    "spec": "----MODULE Action ----\nEXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals\n\nAction == \n  /\\\\ a' = IF a = 1 THEN 2 ELSE a\n====",
    "errors": [
        {
            "error_message": "Encountered \"====\" at line 7, column 1 and token \"2\"",
            "solution": "Convert IF-THEN to complete IF-THEN-ELSE structure. Replace with: a' = IF a = 1 THEN 2 ELSE a",
            "context": "Action == \n  /\\\\ IF a = 1 THEN a' = 2"
        }
    ]
}
```