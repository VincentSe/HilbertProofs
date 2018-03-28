(setq fol-keywords
      '(("EXTENDS\\|CHOOSE\\|BECAUSE\\|PROOF\\|VARIABLES\\|THEOREM\\|PROPO_TAUTO\\|AXIOM_SCHEME\\|Q_SCHEME\\|E_SCHEME\\|AXIOM\\|QED\\|CONSTANT" . font-lock-keyword-face)
        ("UNION\\|SUBSET\\|MODUS_PONENS\\|GENERALIZATION" . font-lock-constant-face)))

;; Defines fol comments. Line comments are \* and block comments are (* *)
(setq fol-syntax-alist
      (list (cons ?* ". 23")
	    (cons ?\n "> c") ;; comment end of "c" style
	    (cons ?\\ ". 1c") ;; \* comment start of "c" style
	    (cons ?( "()1b") ;; (* start sequence of "b" style
	    (cons ?) ")(4b"))) ;; *) end sequence of "b" style

(define-derived-mode fol-mode fundamental-mode "fol"
  "major mode for editing first-order logic proofs."
  (setq font-lock-defaults (list 'fol-keywords
				 nil ;; activate syntactic fontification (for comments)
				 nil ;; case-sensitive
				 fol-syntax-alist)))
