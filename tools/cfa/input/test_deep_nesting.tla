---- MODULE test_deep_nesting ----
VARIABLES x, y, z, w, v, status

// Test case for deep nesting - this should now work correctly with our new junction list implementation
DeepNestedAction ==
    /\ x > 0
    /\ y > 0 
        \/ level2_option1
        \/ level2_option2
            /\ level3_condition1
            /\ level3_condition2
                \/ level4_option1
                \/ level4_option2
                    /\ level5_condition1
                    /\ level5_condition2
    /\ z > 0
    /\ w > 0
    /\ v > 0

// Test case for mixed nesting with statements
ComplexNestedLogic ==
    /\ status = "ready"
    /\ IF x > 5
       THEN /\ y' = y + 1
            /\ z' = z + 1
                \/ backup_option1
                \/ backup_option2
                    /\ deep_backup_condition1
                    /\ deep_backup_condition2
       ELSE /\ x' = x + 1
            /\ status' = "processing"
    /\ result' = "completed"

// Test case for deeply nested disjunction
DeepDisjunctionTest ==
    \/ simple_case
    \/ complex_case_level1
        /\ condition1
        /\ condition2
            \/ nested_case1
            \/ nested_case2
                /\ deep_condition1
                /\ deep_condition2
                    \/ very_deep_case1
                    \/ very_deep_case2
    \/ final_fallback

====