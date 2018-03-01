((coq-mode
  . ((eval . 
	   (let ((unimath-topdir (expand-file-name (locate-dominating-file buffer-file-name "UniMath"))))
	     (setq fill-column 100)
	     (make-local-variable 'coq-use-project-file)
	     (setq coq-use-project-file nil)
	     (make-local-variable 'coq-prog-args)
	     (setq coq-prog-args `("-emacs"
				   "-noinit"
				   "-indices-matter"
				   "-Q" ,(concat unimath-topdir "UniMath") "UniMath"
				   "-w" "-notation-overridden,-local-declaration,+uniform-inheritance,-deprecated-option"
				   ))
	     (if (equal buffer-file-name (concat unimath-topdir "UniMath/Foundations/Resizing.v"))
		 (setq coq-prog-args (cons "-type-in-type" coq-prog-args)))
	     (make-local-variable 'coq-prog-name)
	     (setq coq-prog-name (concat unimath-topdir "sub/coq/bin/coqtop"))
	     (make-local-variable 'before-save-hook)
	     (add-hook 'before-save-hook 'delete-trailing-whitespace)
	     (modify-syntax-entry ?' "w")
	     (modify-syntax-entry ?_ "w")
	     (if (not (memq 'agda-input features))
		 (load (concat unimath-topdir "emacs/agda/agda-input")))
	     (if (not (member '("chimney" "╝") agda-input-user-translations))
		 (progn
		   (setq agda-input-user-translations (cons '("chimney" "╝") agda-input-user-translations))
		   (setq agda-input-user-translations (cons '("==>" "⟹") agda-input-user-translations))
		   (agda-input-setup)))
	     (set-input-method "Agda"))))))
