;;; company-coq-bitstrings.el --- Company-coq extension to prettify bitstrings -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; Keywords: convenience, languages

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Setup:

;; 1. Symlink this file into .emacs.d
;; 2. Add the following to your .emacs:
;;      (load-file "~/.emacs.d/company-coq-bitstrings.el")

;;; Code:

(require 'company-coq)

(defface company-coq-bitstrings-face
  '((t :underline "white"))
  "Face used to highlight bitstrings."
  :group 'company-coq-faces)

(defvar company-coq-bitstrings-show-hex nil
  "Show HEX value of current bits in addition to binary.")

(defun company-coq-bitstrings--bits-display-spec (w _pad-to)
  "Prettify a bitstring W.
_PAD-TO is ignored."
  (let* ((bin (replace-regexp-in-string "[b~]" "" w))
         (num (string-to-number bin 2))
         (str (concat
               "0" (propertize "b" 'face 'font-lock-constant-face) bin
               (if company-coq-bitstrings-show-hex
                   (format " (0%s%x)"
                           (propertize "x" 'face 'font-lock-constant-face) num)))))
    (font-lock-append-text-property
     0 (length str) 'face 'company-coq-bitstrings-face str)
    str))

(defun company-coq-bitstrings--bits-fl-spec ()
  "Compute a font-lock specification for current match."
  (let ((spec (company-coq-bitstrings--bits-display-spec
               (match-string-no-properties 1)
               (- (match-end 0) (match-beginning 0)))))
    `(face nil display ,spec)))

(defconst company-coq-bitstrings--font-lock-keywords
  '(("\\(?:WO\\|Ob\\)\\(\\(?:~[01]\\)+\\)" (0 (company-coq-bitstrings--bits-fl-spec) t))))

(with-eval-after-load 'company-coq
  (company-coq-define-feature bitstrings (arg)
    "Prettify bitstrings."
    (company-coq-do-in-all-buffers
      (add-to-list 'font-lock-extra-managed-props 'display)
      (pcase arg
        (`on (font-lock-add-keywords nil company-coq-bitstrings--font-lock-keywords 'append))
        (`off (font-lock-remove-keywords nil company-coq-bitstrings--font-lock-keywords)))
      (company-coq-request-refontification))))

(provide 'company-coq-bitstrings)
;;; company-coq-bitstrings.el ends here
