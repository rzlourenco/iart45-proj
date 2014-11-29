; Grupo 77
; ist176133 - Rodrigo Lourenco
; ist179515 - Joao Vasco Pestana
; -*- vim: ts=8 sw=4 sts=4 expandtab
(load (compile-file "exemplos.fas"))

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
    (num-restricoes NIL)
    (dirty NIL)
    (atribuicoes NIL))

(defun cria-psr (vars doms restrs)
    (let ((num-vars (list-length vars)))
    (let ((var-doms (make-hash-table :test #'equal :size num-vars))
          (var-doms-assoc (zipWith #'cons vars doms))
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
                   :atribuicoes (make-hash-table :test #'equal)))))

(defun psr-atribuicoes (psr)
    (hash-table-keyvalues (psr-impl-atribuicoes psr)))

(defun psr-variaveis-todas (psr)
    (psr-impl-variaveis psr))

; Nota: remove uma variavel se o seu valor estiver definido (!= NIL)
(defun psr-variaveis-nao-atribuidas (psr)
    (if (psr-impl-dirty psr)
        (let ((newVarList NIL))
            (setf newVarList (remove-if #'(lambda (v) (psr-variavel-valor psr v)) (psr-variaveis-todas psr)))
            (setf (psr-impl-dirty psr) NIL)
            (setf (psr-impl-empty-vars psr) newVarList))
        (psr-impl-empty-vars psr)))

; Nota: gethash devolve NIL se a chave nao estiver presente na hashtable
(defun psr-variavel-valor (psr var)
    (multiple-value-bind (v found)
        (gethash var (psr-impl-atribuicoes psr))
        (declare (ignore found))
        v))

(defun psr-variavel-dominio (psr var)
    (multiple-value-bind (v found)
        (gethash var (psr-impl-var-doms psr))
        (declare (ignore found))
        v))

; Nota: devolve uma copia da lista de restricoes onde todas as restricoes
; devolvidas incluem a variavel especificada.
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

; Nota: se uma restricao nao e verificada, entao nao e necessario verificar mais
; nenhuma. E o que e verificado na primeira forma do cond.
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
    (let ((edges NIL))
    (dolist (nvar (psr-variaveis-nao-atribuidas psr))
        (if (and (not (equal var nvar)) (psr-variaveis-vizinhas-p psr var nvar))
            (setf edges (cons (cons nvar var) edges))))
    (reverse edges)))

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

(defun psr-heuristica-grau-mrv (psr)
    (let ((bestVar NIL)
          (domLen 0)
          (maxCount -1))
    (dolist (var (psr-variaveis-nao-atribuidas psr))
        (let ((restrs (psr-variavel-restricoes psr var))
              (count 0))
        (dolist (restr restrs)
            (dolist (ovar (restricao-variaveis restr))
                (if (and (null (psr-variavel-valor psr ovar)) (not (equal var ovar)))
                    (progn
                        (incf count)
                        (return)))))
        (cond
            ((> count maxCount)
                (setf bestVar  var
                      maxCount count
                      domLen (list-length (psr-variavel-dominio psr var))))
            ((= count maxCount)
                (let ((odomLen (list-length (psr-variavel-dominio psr var))))
                (if (< odomLen domLen)
                    (setf bestVar var
                          domLen  odomLen)))))))
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
                        ; 1o - A soma das variaveis ja atribuidas tem de ser inferior ao valor da restricao
                        ; 2o - Pegamos no caso em que todas as variaveis nao atribuidas sao 1.
                        ; Sendo assim, se os elementos que faltam atribuir nao forem suficientes
                        ; para completar a restricao (ex: um 9 com um 0 a volta, e varias variaveis por
                        ; atribuir) devolve falso.
                        ; (format T "[R] elm: ~A numAttrs: ~A remAttrs: ~A sum: ~A -- ~A~%" elm (list-length vals) remAttrs sum (zipWith #'cons restrVars vals))
                        (and (<= sum elm) (>= (+ remAttrs sum) elm)))))))
        (if restrFun
            (setf restrs (cons (cria-restricao restrVars restrFun) restrs))))))
    (cria-psr (reverse vars) (reverse doms) (reverse restrs))))

(defun fill-a-pix->psr-pistas (arr)
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
            ((and (numberp elm) (>= elm 1) (<= elm 8))
                (setf restrFun
                    #'(lambda (psr)
                        (let ((remAttrs 0)
                              (sum 0))
                        (dolist (var restrVars)
                            (let ((e (psr-variavel-valor psr var)))
                            (if e
                                (incf sum e)
                                (incf remAttrs 1))))
                        ; 1o - A soma das variaveis ja atribuidas tem de ser inferior ao valor da restricao
                        ; 2o - Pegamos no caso em que todas as variaveis nao atribuidas sao 1.
                        ; Sendo assim, se os elementos que faltam atribuir nao forem suficientes
                        ; para completar a restricao (ex: um 9 com um 0 a volta, e varias variaveis por
                        ; atribuir) devolve falso.
                        ; (format T "[R] elm: ~A numAttrs: ~A remAttrs: ~A sum: ~A -- ~A~%" elm (list-length vals) remAttrs sum (zipWith #'cons restrVars vals))
                        (and (<= sum elm) (>= (+ remAttrs sum) elm)))))))
        (if restrFun
            (setf restrs (cons (cria-restricao restrVars restrFun) restrs))))))
    (cria-psr (reverse vars) (reverse doms) (reverse restrs))))

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

(defun procura-retrocesso-grau-mrv (psr)
    (procura-retrocesso-simples psr #'psr-heuristica-grau-mrv))

(defun procura-retrocesso-fc-mrv (psr)
    (procura-retrocesso-propagacao psr #'forward-checking #'psr-heuristica-mrv))

(defun procura-retrocesso-fc-grau (psr)
    (procura-retrocesso-propagacao psr #'forward-checking #'psr-heuristica-grau))

(defun procura-retrocesso-fc-grau-mrv (psr)
    (procura-retrocesso-propagacao psr #'forward-checking #'psr-heuristica-grau-mrv))

(defun procura-retrocesso-fc-mrv-grau (psr)
    (procura-retrocesso-propagacao psr #'forward-checking #'psr-heuristica-mrv-grau))

(defun procura-retrocesso-mac-mrv (psr)
    (procura-retrocesso-propagacao psr #'maintain-arc-consistency #'psr-heuristica-mrv))

(defun procura-retrocesso-mac-grau (psr)
    (procura-retrocesso-propagacao psr #'maintain-arc-consistency #'psr-heuristica-grau))

(defun procura-retrocesso-mac-grau-mrv (psr)
    (procura-retrocesso-propagacao psr #'maintain-arc-consistency #'psr-heuristica-grau-mrv))

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
          (w   (array-dimension arr 1))
          (ii  (- h 1))
          (jj  (- w 1)))
    (dotimes (i h)
    (dotimes (j w)
        (cond
            ; Essencialmente, o 0 e o 9 podem ser vistos como restricoes unarias, logo podemos simplesmente colocar os
            ; respectivos valores, cortando por cada 0 ou 9 o numero de combinacoes possiveis no tabuleiro para 1/16,
            ; pois ha pelo menos 4 variaveis adjacentes, 2^4 combinacoes
            ((equal (aref arr i j) 0)
                (dolist (pos (matrix-adjacent h w i j :self T))
                    (psr-adiciona-atribuicao! psr (variavel-nome w pos) 0)))
            ; Podemos aplicar a mesma logica para 4 e 6. Se o 4 esta num canto, entao podemos preencher todas as
            ; quadriculas adjacentes. O mesmo para um 6 que esteja numa aresta.
            ((equal (aref arr i j) 4)
                (if (or (and (= i 0) (or (= j 0) (= j jj))) (and (= i ii) (or (= j 0) (= j jj))))
                    (dolist (pos (matrix-adjacent h w i j :self T))
                        (psr-adiciona-atribuicao! psr (variavel-nome w pos) 1))))
            ((equal (aref arr i j) 6)
                (if (or (= i 0) (= j 0) (= i ii) (= j jj))
                    (dolist (pos (matrix-adjacent h w i j :self T))
                        (psr-adiciona-atribuicao! psr (variavel-nome w pos) 1))))
            ((equal (aref arr i j) 9)
                (dolist (pos (matrix-adjacent h w i j :self T))
                    (psr-adiciona-atribuicao! psr (variavel-nome w pos) 1))))))
    (psr->fill-a-pix
        (funcall fun psr)
        h
        w)))

; =============================================================================
; = Funcoes auxiliares                                                        =
; =============================================================================

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

; Aceita uma hash-table e devolve uma lista de todos os pares (chave valor)
; na tabela.
(defun hash-table-keyvalues (table)
    (let ((lst ()))
    (maphash #'(lambda (k v) (setf lst (cons (cons k v) lst))) table)
    lst))

; Algumas funcoes de alta ordem que dao jeito e nao ha em Lisp
(defun repeat (count val)
    (cond
        ((= count 0)
            NIL)
        (T
            (cons val (repeat (- count 1) val)))))

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
    (let ((positions (repeat 9 (cons line column)))
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
