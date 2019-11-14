(defmacro module (name &rest body)
  (declare (indent defun)))

(defmacro rule (name args &rest body)
  (declare (indent defun)))

(defmacro scheduler (&rest body)
  (declare (indent defun)))

(defmacro register (name value))

(defmacro enum (name &rest body)
  (declare (indent 1)))

(defmacro struct (name &rest body)
  (declare (indent 1)))

(defmacro switch (arg &rest body)
  (declare (indent 1)))

(defmacro extfun (name args ret))

(defmacro cpp-preamble (s))
(defmacro sequence (s))

(defmacro read.0 (name))
(defmacro write.0 (name val)
  (declare (indent 1)))

(defmacro read.1 (name))
(defmacro write.1 (name val)
  (declare (indent 1)))

(defun zextl (nbits arg)
  (declare (indent 1)))

(require 'flycheck nil t)
(require 'imenu nil t)

(defconst lv-script-full-path
  (or (and load-in-progress load-file-name)
      (bound-and-true-p byte-compile-current-file)
      (buffer-file-name))
  "Full path of this script.")

(defconst lv-script-root-path
  (file-name-directory lv-script-full-path))

(defun lv--make-imenu-expression (name headers ngroup)
  "Construct a (NAME HEADERS NGROUP) form for `imenu-generic-expression'."
  (list name (format "^\\s-*(\\(\\_<%s\\_> \\_<\\(.*?\\)\\_>\\)" (regexp-opt headers nil)) ngroup))

;; (defun lv--scan-buffer ()
;;   "Scan the buffer to build an outline."
;;   (goto-char (point-min))
;;   (let ((doctree (make-hash-table)))
;;     (puthash nil ("root" . nil) doctree)
;;     (while (re-search-forward lv--outline-header-re nil t)
;;       (let* ((address (match-beginning 0))
;;              (stx (syntax-ppss address))
;;              (in-string (nth 3 stx))
;;              (in-comment (nth 4 stx))
;;              (parents (reverse (nth 9 stx)))
;;              (doctree-node nil))
;;         (unless (or in-string in-comment)
;;           (while (null doctree-node)
;;             ;; If none of the parents are in the doctree, `pop' will eventually
;;             ;; return nil, which maps to the root of the document in doctree.
;;             (setq doctree-node (gethash (pop parents) doctree)))
;;           (push address (cdr doctree-node)) ;; FIXME create a marker?
;;           )
;;         )
;;       )))

(defvar lv--imenu-generic-expression
  (list (lv--make-imenu-expression "Modules" '("module" "register" "rule" "scheduler") 1)
        (lv--make-imenu-expression "Declarations" '("struct" "enum") 1)
        (lv--make-imenu-expression "External functions" '("extfun") 2))
  "`imenu-generic-expression' for lv-mode.")

(flycheck-define-checker lv
  "A checker for Lispy Verilog."
  :command ("cuttlec.exe" "-")
  :standard-input t
  :error-patterns
  ((error line-start
          (file-name)
          ":" line (? "-" (1+ digit))
          ":" column (? "-" (1+ digit))
          ":" (0+ blank) (id (minimal-match (1+ not-newline)) "error")
          ":" (message) line-end)
   (warning line-start
            (file-name)
            ":" line (? "-" (1+ digit))
            ":" column (? "-" (1+ digit))
            ":" (0+ blank) "Warning"
            ":" (message) line-end))
  :error-filter
  (lambda (errors)
    (flycheck-sanitize-errors
     (flycheck-remove-error-file-names "-" errors)))
  :modes lispy-verilog-mode)

(setf (car (flycheck-checker-get 'lv 'command))
      (expand-file-name "_build/default/ocaml/cuttlec.exe"
                        (file-name-directory (directory-file-name lv-script-root-path))))

(add-to-list 'flycheck-checkers 'lv)

(define-derived-mode lispy-verilog-mode emacs-lisp-mode "LV"
  (flycheck-mode 1)
  (setq-local imenu-generic-expression lv--imenu-generic-expression)
  (imenu-add-menubar-index))

(add-to-list 'auto-mode-alist '("\\.lv\\'" . lispy-verilog-mode))
