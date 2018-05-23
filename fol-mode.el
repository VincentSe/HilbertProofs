(setq fol-keywords
      '(("LOCAL\\|EXTENDS\\|CHOOSE_UNIQUE\\|CHOOSE\\|BECAUSE\\|PROOF\\|VARIABLES\\|THEOREM\\|PROPO_TAUTO\\|AXIOM_SCHEME\\|Q_SCHEME\\|E_SCHEME\\|AXIOM\\|MACRO\\|QED\\|CONSTANT" . font-lock-keyword-face)
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

(define-key fol-mode-map (kbd "<f7>") 'compile)

(defun fol-theo-dfn (theo)
  (save-excursion
    (goto-char (point-min))
    (let ((beg (search-forward (concat theo " == ") nil t))
	  (end (or (search-forward (concat "THEOREM " theo) nil t)
		   (search-forward (concat "AXIOM " theo) nil t))))
      (and beg
	   end
	   (buffer-substring beg (progn (backward-word 2) (point)))))))

(defun fol-invoke-theorem (theo)
  "Insert theo BECAUSE THEOREM; and the definition of theo"
  (interactive "sTheorem name: ")
  (let ((d (fol-theo-dfn theo)))
    (if d
      (insert theo "   BECAUSE THEOREM;\n"
	      d "   BECAUSE ")
      (error (concat theo " not found")))))
