(in-package #:sat-protocol/conformance)

;;; The decision-order hook reproduces cl-repository's latest-version-first
;;; choice (brief: order-hook-test). cl-repository reads the T bindings of a
;;; partial model, so the call is :order #'latest-first-order :phase :true
;;; :complete nil. Expected selections are what cl-repository's SAT-SOLVE picks
;;; on the same formulas (worked by hand; the reference backend is that search).

(defun resolve (formula)
  (multiple-value-bind (model sat)
      (solve formula :order #'latest-first-order :phase :true :complete nil)
    (and sat (true-names model))))

(deftest latest-first-order-rule
  (ok (string= "foo-v2" (latest-first-order '("foo-v1" "foo-v2"))))
  (ok (string= "foo-v1.10" (latest-first-order '("foo-v1.9" "foo-v1.10"))) "1.10 after 1.9")
  (ok (string= "zlib-v1" (latest-first-order '("app-v9" "zlib-v1"))) "package name first"))

(deftest order-hook-prefers-latest
  ;; cl-repository tests/client/solver-test.lisp test-solve-latest-version-heuristic
  (ok (equal '("foo-v2")
             (resolve (f '(:and (:or "foo-v1" "foo-v2") (:not (:and "foo-v1" "foo-v2"))))))))

(deftest order-hook-semantic-version
  (ok (equal '("app-v1.0" "lib-v1.10")
             (resolve (package-formula :root '("app" "1.0")
                                       :packages '(("app" "1.0") ("lib" "1.9" "1.10" "1.2"))
                                       :depends '(("app" "1.0" "lib" "1.9" "1.10" "1.2")))))))

(deftest order-hook-pinned-forces-older
  ;; lib 2.0 needs z 2.0, but z 1.0 is installed (pinned): lib 1.0 is chosen.
  (ok (equal '("app-v1.0" "lib-v1.0" "z-v1.0")
             (resolve (package-formula :root '("app" "1.0")
                                       :packages '(("app" "1.0") ("lib" "1.0" "2.0") ("z" "1.0" "2.0"))
                                       :depends '(("app" "1.0" "lib" "1.0" "2.0")
                                                  ("lib" "2.0" "z" "2.0")
                                                  ("lib" "1.0" "z" "1.0" "2.0"))
                                       :pins '(("z" "1.0")))))))

(deftest order-hook-diamond
  ;; c is the last package, so its latest version is decided first; b 2.0 needs
  ;; c 1.0, so b falls back to 1.0; a takes its latest.
  (ok (equal '("a-v2" "app-v1" "b-v1" "c-v2")
             (resolve (package-formula :root '("app" "1")
                                       :packages '(("app" "1") ("a" "1" "2") ("b" "1" "2") ("c" "1" "2"))
                                       :depends '(("app" "1" "a" "1" "2")
                                                  ("app" "1" "b" "1" "2")
                                                  ("a" "2" "c" "2")
                                                  ("b" "1" "c" "1" "2")
                                                  ("b" "2" "c" "1")))))))

(deftest order-hook-conflict-is-unsat
  (ok (null (resolve (package-formula :root '("app" "1")
                                      :packages '(("app" "1") ("x" "1" "2"))
                                      :depends '(("app" "1" "x" "2"))
                                      :pins '(("x" "1")))))))

(deftest order-hook-clause-shaped-formula-has-no-auxiliaries
  ;; cl-repository's formula shape converts clause by clause, so the hook sees
  ;; every package variable.
  (let ((cnf (to-cnf (package-formula :root '("app" "1")
                                      :packages '(("app" "1") ("x" "1" "2"))
                                      :depends '(("app" "1" "x" "1" "2"))))))
    (ok (notany (lambda (i) (cnf-aux-variable-p cnf i))
                (loop for i from 1 to (cnf-variable-count cnf) collect i)))))
