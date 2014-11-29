; Grupo 77
; ist176133 - Rodrigo Lourenco
; ist179515 - Joao Vasco Pestana
; -*- vim: ts=8 sw=4 sts=4 expandtab
(load "exemplos.fas")

; =============================================================================
; = Restricao                                                                 =
; =============================================================================

; Restricao: uma de lista de variaveis e um predicado que verifica um psr
(defstruct (restricao (:constructor cria-restricao (variaveis funcao-validacao)))
    (variaveis NIL)
    (funcao-validacao #'(lambda (psr) (declare (ignore psr)) T)))

; =============================================================================
; = PSR                                                                       =
; =============================================================================

; PSR: um problema de satisfacao de restricoes
(defstruct psr-impl
    (variaveis NIL)
    (num-vars 0)
    (restricoes NIL)
    (var-doms NIL)
    (var-restrs NIL)
    (empty-vars NIL)
    (dirty NIL)
    (atribuicoes NIL))

(defun cria-psr (vars doms restrs)
    (let ((num-vars (list-length vars)))
    (let ((var-doms (make-hash-table :test #'equal :size num-vars))
          (var-doms-assoc (pairlis vars doms))
          (var-restrs (make-hash-table :test #'equal :size num-vars)))

    (dolist (e var-doms-assoc)
        (setf (gethash (car e) var-doms) (cdr e)))

    (dolist (restr restrs)
        (dolist (var (restricao-variaveis restr))
            (let ((prev (gethash var var-restrs)))
            (setf (gethash var var-restrs) (cons restr prev)))))

    (maphash
        #'(lambda (k v)
            (setf (gethash k var-restrs) (reverse v)))
        var-restrs)

    (make-psr-impl :variaveis vars
                   :num-vars num-vars
                   :restricoes restrs
                   :var-doms var-doms
                   :var-restrs var-restrs
                   :empty-vars vars
                   :dirty NIL
                   :atribuicoes (make-hash-table :test #'equal :size num-vars)))))

(defun psr-atribuicoes (psr)
    (let ((lst ()))
    (maphash #'(lambda (k v) (setf lst (cons (cons k v) lst))) (psr-impl-atribuicoes psr))
    lst))

(defun psr-variaveis-todas (psr)
    (psr-impl-variaveis psr))

; Nota: gethash devolve NIL se a chave nao estiver presente na hashtable
(defun psr-variavel-valor (psr var)
    (multiple-value-bind (v found)
        (gethash var (psr-impl-atribuicoes psr))
        (declare (ignore found))
        v))

(defun psr-variaveis-nao-atribuidas (psr)
    (if (psr-impl-dirty psr)
        (let ((newVarList NIL))
            (setf newVarList (remove-if #'(lambda (v) (psr-variavel-valor psr v)) (psr-variaveis-todas psr)))
            (setf (psr-impl-dirty psr) NIL)
            (setf (psr-impl-empty-vars psr) newVarList))
        (psr-impl-empty-vars psr)))

(defun psr-variavel-dominio (psr var)
    (multiple-value-bind (v found)
        (gethash var (psr-impl-var-doms psr))
        (declare (ignore found))
        v))

(defun psr-variavel-restricoes (psr var)
    (multiple-value-bind (v found)
        (gethash var (psr-impl-var-restrs psr))
        (declare (ignore found))
        v))

(defun psr-adiciona-atribuicao! (psr var val)
    (setf (psr-impl-dirty psr) T)
    (setf (gethash var (psr-impl-atribuicoes psr)) val)
    NIL)

(defun psr-remove-atribuicao! (psr var)
    (setf (psr-impl-dirty psr) T)
    (remhash var (psr-impl-atribuicoes psr))
    NIL)

(defun psr-altera-dominio! (psr var dom)
    (setf (gethash var (psr-impl-var-doms psr)) dom)
    NIL)

(defun psr-completo-p (psr)
    (let ((hashcnt (hash-table-count (psr-impl-atribuicoes psr)))
          (numvars (psr-impl-num-vars psr)))
    (equal hashcnt numvars)))

(defun psr-consistente-p (psr)
    (let ((restrcount 0))
    (dolist (restr (psr-impl-restricoes psr))
        (incf restrcount)
        (if (not (funcall (restricao-funcao-validacao restr) psr))
            (return-from psr-consistente-p (values NIL restrcount))))
    (values T restrcount)))

(defun psr-variavel-consistente-p (psr var)
    (let ((restrcount 0))
    (dolist (restr (psr-variavel-restricoes psr var))
        (incf restrcount)
        (if (not (funcall (restricao-funcao-validacao restr) psr))
            (return-from psr-variavel-consistente-p (values NIL restrcount))))
    (values T restrcount)))

; Nota: aqui fazemos uma atribuicao temporaria, testando a seguir todas as
; restricoes que envolvem a dada variavel.
(defun psr-atribuicao-consistente-p (psr var val)
    (let ((oldval (psr-variavel-valor psr var))
          (ret NIL))
    (psr-adiciona-atribuicao! psr var val)
    (setf ret (multiple-value-list (psr-variavel-consistente-p psr var)))

    (if oldval
        (psr-adiciona-atribuicao! psr var oldval)
        (psr-remove-atribuicao! psr var))

    (values-list ret)))

; Nota: utilizamos a interseccao das restricoes das variaveis para evitar verificar
; mais do que uma vez a mesma restricao.
(defun psr-atribuicoes-consistentes-arco-p (psr var1 val1 var2 val2)
    (let ((restrcount 0)
          (oldval1 (psr-variavel-valor psr var1))
          (oldval2 (psr-variavel-valor psr var2))
          (result T))
    (psr-adiciona-atribuicao! psr var1 val1)
    (psr-adiciona-atribuicao! psr var2 val2)

    (dolist (restr (psr-variavel-restricoes psr var1))
        (if (find var2 (restricao-variaveis restr) :test #'equal)
            (progn
                (incf restrcount)
                (if (not (funcall (restricao-funcao-validacao restr) psr))
                    (progn
                        (setf result NIL)
                        (return))))))

    (if oldval1
        (psr-adiciona-atribuicao! psr var1 oldval1)
        (psr-remove-atribuicao! psr var1))
    (if oldval2
        (psr-adiciona-atribuicao! psr var2 oldval2)
        (psr-remove-atribuicao! psr var2))

    (values result restrcount)))

; ============================================================================
; = Extensoes ao tipo PSR                                                    =
; ============================================================================

(defun psr-variaveis-vizinhas-p (psr var1 var2)
    (dolist (restr (psr-variavel-restricoes psr var1))
        (if (find var2 (restricao-variaveis restr) :test #'equal)
            (return-from psr-variaveis-vizinhas-p T)))
    NIL)

(defun psr-arcos-vizinhos-nao-atribuidos (psr var)
    (let ((neighbours (make-hash-table :test #'equal)))
    (dolist (restr (psr-variavel-restricoes psr var))
        (dolist (var2 (restricao-variaveis restr))
            (setf (gethash var2 neighbours) T)))
    (let ((edges NIL))
    (dolist (nvar (psr-variaveis-nao-atribuidas psr))
        (if (and (not (equal var nvar)) (gethash nvar neighbours))
            (setf edges (cons (cons nvar var) edges))))
    (reverse edges))))

; =============================================================================
; = Funcoes auxiliares                                                        =
; =============================================================================

(defun zipWith (f xs ys)
    (cond
        ((or (null xs) (null ys))
            NIL)
        (T
            (cons (funcall f (first xs) (first ys))
            (zipWith f (rest xs) (rest ys))))))

(defun variavel-nome (columns pos)
    ; (format NIL "(~D,~D)" (car pos) (cdr pos)))
    (+ (* columns (car pos)) (cdr pos)))

(defun matrix-adjacent (height width line column &key (self NIL))
    (let ((positions (make-list 9 :initial-element (cons line column)))
          (deltas (list '(-1 . -1) '(-1 . 0) '(-1 . 1)
                        '( 0 . -1) '( 0 . 0) '( 0 . 1)
                        '( 1 . -1) '( 1 . 0) '( 1 . 1))))
    (decf width)
    (decf height)
    (zipWith
        #'(lambda (l r) (cons (+ (car l) (car r)) (+ (cdr l) (cdr r))))
        (remove-if
            #'(lambda (delta)
                (let ((dy (car delta))
                      (dx (cdr delta)))
                (cond
                    ((and (= line height) (= dy 1)) T)
                    ((and (= line 0) (= dy -1)) T)
                    ((and (= column width) (= dx 1)) T)
                    ((and (= column 0) (= dx -1)) T)
                    ((and (not self) (= dx 0) (= dy 0)) T))))
            deltas)
        positions)))


; =============================================================================
; = Funcoes de conversao                                                      =
; =============================================================================

(defun fill-a-pix->psr (arr)
    (let ((vars NIL)
          (doms NIL)
          (restrs NIL))
    (dotimes (i (array-dimension arr 0))
    (dotimes (j (array-dimension arr 1))
        (setf vars (cons (variavel-nome (array-dimension arr 1) (cons i j)) vars)
              doms (cons (list 0 1) doms))
        (let ((elm (aref arr i j))
              (restrFun NIL)
              (restrVars (mapcar
                            #'(lambda (pos) (variavel-nome (array-dimension arr 1) pos))
                            (matrix-adjacent
                                (array-dimension arr 0)
                                (array-dimension arr 1)
                                i j :self T))))
        (cond
            ((and (numberp elm) (>= elm 0) (<= elm 9))
                (setf restrFun
                    #'(lambda (psr)
                        (let ((remAttrs 0)
                              (sum 0))
                        (dolist (var restrVars)
                            (let ((e (psr-variavel-valor psr var)))
                            (if e
                                (incf sum e)
                                (incf remAttrs 1))))
                        (and (<= sum elm) (>= (+ remAttrs sum) elm)))))))
        (if restrFun
            (setf restrs (cons (cria-restricao restrVars restrFun) restrs))))))
    (cria-psr (reverse vars) (reverse doms) (reverse restrs))))

(defun fill-a-pix->psr-pistas (arr)
    (let ((vars NIL)
          (doms NIL)
          (restrs NIL)
          (bestVars NIL)
          (bestDoms NIL)
          (bestPos NIL)
          (psr NIL))
    (dotimes (i (array-dimension arr 0))
    (dotimes (j (array-dimension arr 1))
        (let* ((elm (aref arr i j))
               (restrFun NIL)
               (varName (variavel-nome (array-dimension arr 1) (cons i j)))
               (restrVars (mapcar
                      #'(lambda (pos) (variavel-nome (array-dimension arr 1) pos))
                          (matrix-adjacent
                              (array-dimension arr 0)
                              (array-dimension arr 1)
                              i j :self T))))
        (cond
            ((not (numberp elm))
                (setf vars (cons varName vars)
                      doms (cons (list 0 1) doms)))
            ((and (>= elm 0) (<= elm 9))
                (if (or (= elm 0) (= (list-length restrVars) elm))
                    (setf bestVars (cons varName bestVars)
                          bestDoms (cons (list (if (= elm 0) 0 1)) bestDoms)
                          bestPos  (cons (cons i j) bestPos))
                    (setf vars (cons varName vars)
                          doms (cons (if (> elm 4) (list 1 0) (list 0 1)) doms)
                          restrFun #'(lambda (psr)
                                        (let ((remAttrs 0)
                                              (sum 0))
                                        (dolist (var restrVars)
                                            (let ((e (psr-variavel-valor psr var)))
                                            (if e
                                                (incf sum e)
                                                (incf remAttrs 1))))
                                        (and (<= sum elm) (>= (+ remAttrs sum) elm))))))))
        (if restrFun
            (setf restrs (cons (cria-restricao restrVars restrFun) restrs))))))
    (setf psr (cria-psr (append vars bestVars) (append doms bestDoms) restrs))
    ; Nas bestVars so ha um valor no dominio, preencher e propagar dominios. Podemos propagar estas inferencias porque
    ; sabemos que os valores atribuidos aqui sao correctos (porque so existe um valor no dominio). Caso contrario, nao
    ; ha solucao para o fill-a-pix.
    (dolist (pos bestPos)
        (let* ((var (variavel-nome (array-dimension arr 1) pos))
               (poss (matrix-adjacent (array-dimension arr 0) (array-dimension arr 1) (car pos) (cdr pos)))
               (nvars (cons var (mapcar #'(lambda (npos) (variavel-nome (array-dimension arr 1) npos)) poss))))
        (dolist (nvar nvars)
            (psr-adiciona-atribuicao! psr nvar (car (psr-variavel-dominio psr var))))))
    (dolist (pos bestPos)
        (let* ((var (variavel-nome (array-dimension arr 1) pos))
               (poss (matrix-adjacent (array-dimension arr 0) (array-dimension arr 1) (car pos) (cdr pos)))
               (nvars (cons var (mapcar #'(lambda (npos) (variavel-nome (array-dimension arr 1) npos)) poss))))
        (dolist (nvar nvars)
            (let ((infs (maintain-arc-consistency psr nvar)))
            (maphash
                #'(lambda (k v)
                    (psr-altera-dominio! psr k v)
                    (if (= 1 (list-length v))
                        (psr-adiciona-atribuicao! psr k (car v))))
                infs)))))
    psr))

(defun psr->fill-a-pix (psr l c)
    (let ((rows NIL)
          (currentRow NIL))
    (dotimes (i l)
        (dotimes (j c)
            (setf currentRow (cons (psr-variavel-valor psr (variavel-nome c (cons i j))) currentRow)))
            (setf rows       (cons (reverse currentRow) rows)
              currentRow NIL))
    (make-array (list l c) :initial-contents (reverse rows))))

; =============================================================================
; = Funcoes de propagacao de restricoes                                       =
; =============================================================================

(defun revise (psr var1 var2 doms)
    (let ((numTests 0)
          (dirty NIL)
          (dom1 (gethash var1 doms))
          (newdom1 NIL)
          (dom2 (gethash var2 doms)))
    (if (null dom1)
        (setf dom1 (psr-variavel-dominio psr var1)))
    (if (psr-variavel-valor psr var2)
        (setf dom2 (list (psr-variavel-valor psr var2)))
        (if (null dom2)
            (setf dom2 (psr-variavel-dominio psr var2))))

    (dolist (val1 dom1)
        (let ((valid NIL))
        (dolist (val2 dom2)
            (multiple-value-bind (consistent tests) (psr-atribuicoes-consistentes-arco-p psr var1 val1 var2 val2)
            (setf valid consistent)
            (incf numTests tests)
            (if valid
                (return))))
        (if valid
            (setf newdom1 (cons val1 newdom1))
            (setf dirty T))))

    (setf newdom1 (reverse newdom1))

    (if dirty
        (setf (gethash var1 doms) newdom1))
    (values dirty numTests)))

(defun forward-checking (psr var)
    (let ((numTests 0)
          (inferences (make-hash-table :test #'equal))
          (edgeList (psr-arcos-vizinhos-nao-atribuidos psr var)))

    (dolist (edge edgeList)
        (let ((var2 (car edge))
              (var1 (cdr edge)))
        (multiple-value-bind (dirty cnt) (revise psr var2 var1 inferences)
        (incf numTests cnt)
        (if dirty
            (if (equal 0 (list-length (gethash var2 inferences)))
                (return-from forward-checking (values NIL numTests)))))))

    (values inferences numTests)))

(defun maintain-arc-consistency (psr var)
    (let ((numTests 0)
          (inferences (make-hash-table :test #'equal))
          (edgeList (psr-arcos-vizinhos-nao-atribuidos psr var)))

    (do (edge var1 var2)
    ((null edgeList))
        (setf edge     (car edgeList)
              var2     (car edge)
              var1     (cdr edge)
              edgeList (cdr edgeList))
        (multiple-value-bind (dirty cnt) (revise psr var2 var1 inferences)
        (incf numTests cnt)
        (if dirty
            (progn
                (if (equal 0 (list-length (gethash var2 inferences)))
                        (return-from maintain-arc-consistency (values NIL numTests)))
                (let ((newEdges NIL))
                (setf newEdges (remove-if
                                    #'(lambda (e)
                                        (and (equal (car e) var1) (equal (cdr e) var2)))
                                    (psr-arcos-vizinhos-nao-atribuidos psr var2)))
                (setf edgeList (append edgeList newEdges)))))))

    (values inferences numTests)))

; ============================================================================
; = Funcoes heuristicas                                                      =
; ============================================================================

(defun psr-heuristica-ordem (psr)
    (car (psr-variaveis-nao-atribuidas psr)))

(defun psr-heuristica-mrv (psr)
    (let ((bestVar NIL)
          (minCount -1))
    (dolist (var (psr-variaveis-nao-atribuidas psr))
        (let ((domlen (list-length (psr-variavel-dominio psr var))))
        (if (or (= minCount -1) (< domlen minCount))
            (progn
                (setf bestVar  var
                      minCount domlen)))))
    bestVar))

(defun psr-heuristica-grau (psr)
    (let ((bestVar NIL)
          (maxCount -1))
    (dolist (var (psr-variaveis-nao-atribuidas psr))
        (let* ((restrs (psr-variavel-restricoes psr var))
               (count 0))
        (dolist (restr restrs)
            (dolist (ovar (restricao-variaveis restr))
                (if (and (null (psr-variavel-valor psr ovar)) (not (equal var ovar)))
                    (progn
                        (incf count)
                        (return)))))
        (if (> count maxCount)
            (setf bestVar  var
                  maxCount count))))
    bestVar))

(defun psr-heuristica-mrv-grau (psr)
    (let ((bestVar NIL)
          (domLen -1)
          (maxCount -1))
    (dolist (var (psr-variaveis-nao-atribuidas psr))
        (let ((restrs (psr-variavel-restricoes psr var))
              (odomLen (list-length (psr-variavel-dominio psr var)))
              (count 0))
        (dolist (restr restrs)
            (dolist (ovar (restricao-variaveis restr))
                (if (not (or (psr-variavel-valor psr ovar) (equal var ovar)))
                    (progn
                        (incf count)
                        (return)))))
        (cond
            ((or (= domLen -1) (< odomLen domLen))
                (setf bestVar  var
                      maxCount count
                      domLen odomLen))
            ((= odomLen domLen)
                (if (> count maxCount)
                    (setf bestVar var
                          maxCount count))))))
    bestVar))

; =============================================================================
; = Funcoes de procura                                                        =
; =============================================================================

(defun procura-retrocesso-simples (psr &optional (heur #'psr-heuristica-ordem) (count 0))
    (let ((var (funcall heur psr)))
    (if var
        (progn
            (dolist (val (psr-variavel-dominio psr var))
                (multiple-value-bind (check cnt) (psr-atribuicao-consistente-p psr var val)
                (incf count cnt)
                (if check
                    (progn
                        (psr-adiciona-atribuicao! psr var val)
                        (multiple-value-bind (newpsr total) (procura-retrocesso-simples psr heur count)
                        (if newpsr
                            (return-from procura-retrocesso-simples (values newpsr total))
                            (setf count total)))))))
            (psr-remove-atribuicao! psr var)
            (values NIL count))
        (values psr count))))

(defun procura-retrocesso-propagacao (psr prop heur &optional (count 0))
    (let ((var (funcall heur psr)))
    (if var
        (progn
            (dolist (val (psr-variavel-dominio psr var))
                (multiple-value-bind (check cnt) (psr-atribuicao-consistente-p psr var val)
                (incf count cnt)
                (if check
                    (progn
                        (psr-adiciona-atribuicao! psr var val)
                        (let ((backup (make-hash-table :test #'equal)))
                        (multiple-value-bind (newdoms fcchecks) (funcall prop psr var)
                        (incf count fcchecks)
                        (if newdoms
                            (progn
                                (maphash
                                    #'(lambda (k v)
                                        (setf (gethash k backup) (psr-variavel-dominio psr k))
                                        (psr-altera-dominio! psr k v))
                                    newdoms)
                                (multiple-value-bind (res totalCount) (procura-retrocesso-propagacao psr prop heur count)
                                (if res
                                    (return-from procura-retrocesso-propagacao (values res totalCount)))
                                (setf count totalCount)
                                (maphash #'(lambda (k v) (psr-altera-dominio! psr k v)) backup))))))))))
            (psr-remove-atribuicao! psr var)
            (values NIL count))
        (values psr count))))

(defun procura-retrocesso-grau (psr)
    (procura-retrocesso-simples psr #'psr-heuristica-grau))

(defun procura-retrocesso-fc-mrv (psr)
    (procura-retrocesso-propagacao psr #'forward-checking #'psr-heuristica-mrv))

(defun procura-retrocesso-fc-mrv-grau (psr)
    (procura-retrocesso-propagacao psr #'forward-checking #'psr-heuristica-mrv-grau))

(defun procura-retrocesso-mac-mrv (psr)
    (procura-retrocesso-propagacao psr #'maintain-arc-consistency #'psr-heuristica-mrv))

(defun procura-retrocesso-mac-mrv-grau (psr)
    (procura-retrocesso-propagacao psr #'maintain-arc-consistency #'psr-heuristica-mrv-grau))

(defun resolve-simples (arr &key (fun #'procura-retrocesso-simples))
    (psr->fill-a-pix
        (funcall fun (fill-a-pix->psr arr))
        (array-dimension arr 0)
        (array-dimension arr 1)))

(defun resolve-best (arr &key (fun #'procura-retrocesso-fc-mrv-grau))
    (let* ((psr (fill-a-pix->psr-pistas arr))
          (h   (array-dimension arr 0))
          (w   (array-dimension arr 1)))
    (psr->fill-a-pix
        (funcall fun psr)
        h
        w)))
