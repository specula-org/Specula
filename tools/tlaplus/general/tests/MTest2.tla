------------------------------- MODULE MTest2 ------------------------------- 

(* Generate error in cfg file that TLC finds 
Model 2: generates TLC error: TLC cannot handle this conjunct of the spec.
Model 3: generates:  Temporal formulas containing actions must be of forms 
         <>[]A or []<>A
*)

VARIABLE x

foo == 1
=============================================================================
