import EML

open EML EML.EMLTerm

-- Headline Path-C′ full-domain trig (witness-family)
#print axioms paper_claim_sin_full
#print axioms paper_claim_arctan_full
#print axioms paper_claim_tan_full

-- Trig (single structural witness on open domain)
#print axioms paper_claim_cos
#print axioms paper_claim_sin
#print axioms paper_claim_arccos_open
#print axioms paper_claim_arcsin_open

-- Real unaries / sqrt
#print axioms paper_claim_sqrt_pos

-- §G witness-family seals (in namespace EML.EMLTerm)
#print axioms paper_claim_sqrt_full
#print axioms paper_claim_arcosh_full
#print axioms paper_claim_hypot_full

-- Frontier modules
#print axioms identity_terms_at_depth_multiples_of_four
#print axioms no_polynomial_binary_generates_exp
#print axioms polynomial_binary_terms_are_polynomial
#print axioms edl_closed_eval_in_closedVal

-- Alternative direct-macro witnesses (in namespace EML.EMLTerm)
#print axioms paper_claim_mul_compact
#print axioms K_count_logb_compact

-- Sheffer cousins
#print axioms edl_paper_claim_log
#print axioms negEml_paper_claim_minusInf
