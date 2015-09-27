((coq-mode
  . ((eval . 
	   (let ((unimath-topdir (expand-file-name (locate-dominating-file buffer-file-name "UniMath"))))
	     (make-local-variable 'coq-use-project-file)
	     (setq coq-use-project-file nil)
	     (make-local-variable 'coq-prog-args)
	     (setq coq-prog-args `("-emacs" "-indices-matter" "-type-in-type" "-R" ,(concat unimath-topdir "UniMath") "UniMath" ))
	     (make-local-variable 'coq-prog-name)
	     (setq coq-prog-name (concat unimath-topdir "sub/coq/bin/coqtop"))
	     (if (not (memq 'agda-input features)) (load (concat unimath-topdir "emacs/agda/agda-input")))
	     (set-input-method "Agda"))))))
