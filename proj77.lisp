; Grupo 77
; ist176133 - Rodrigo Lourenco
; ist179515 - Joao Vasco Pestana
; -*- vim: ts=8 sw=2 sts=2 expandtab
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
    (num-restricoes NIL)
    (atribuicoes NIL))

(defun cria-psr (vars doms restrs)
    (let ((var-doms (make-hash-table :test #'equal))
          (num-restricoes (make-hash-table :test #'equal))
          (var-doms-assoc (zipWith #'cons vars doms)))

    (dolist (e var-doms-assoc)
        (setf (gethash (car e) num-restricoes) 0)
        (setf (gethash (car e) var-doms) (cdr e)))

    (dolist (restr restrs)
        (dolist (var (restricao-variaveis restr))
            (incf (gethash var num-restricoes 0))))

    (make-psr-impl :variaveis vars
                   :num-vars (list-length vars)
                   :restricoes restrs
                   :var-doms var-doms
                   :num-restricoes num-restricoes
                   :atribuicoes (make-hash-table :test #'equal))))

(defun psr-atribuicoes (psr)
    (hash-table-keyvalues (psr-impl-atribuicoes psr)))

(defun psr-variaveis-todas (psr)
    (psr-impl-variaveis psr))

; Nota: remove uma variavel se o seu valor estiver definido (!= NIL)
(defun psr-variaveis-nao-atribuidas (psr)
    (remove-if
        #'(lambda (v) (psr-variavel-valor psr v))
        (psr-variaveis-todas psr)))

; Nota: gethash devolve NIL se a chave nao estiver presente na hashtable
(defun psr-variavel-valor (psr var)
    (multiple-value-bind (v found)
        (gethash var (psr-impl-atribuicoes psr))
        (declare (ignore found))
        v))

(defun psr-variavel-dominio (psr var)
    (multiple-value-bind (v found)
        (gethash var (psr-impl-var-doms psr))
        (if (null found)
            (error (format NIL "psr-variavel-dominio: var ~A has no domain" var) T))
            v))

; Nota: devolve uma copia da lista de restricoes onde todas as restricoes
; devolvidas incluem a variavel especificada.
(defun psr-variavel-restricoes (psr var)
    (remove-if
        #'(lambda (r)
            (not (find var (restricao-variaveis r) :test #'equal)))
        (psr-impl-restricoes psr)))

(defun psr-variavel-num-restricoes (psr var)
    (multiple-value-bind (v found)
        (gethash var (psr-impl-num-restricoes psr))
        (declare (ignore found))
        v))

; Nota: visto que o valor de uma variavel nao definida e NIL, entao vamos
; aproveitar para simplificar algum codigo que faz modificaoes temporarias ao
; permitir que atribuir NIL a uma variavel a apague, sendo desnecessario o teste
; a NIL do valor anterior seguido de uma remocao.
(defun psr-adiciona-atribuicao! (psr var val)
    (setf (gethash var (psr-impl-atribuicoes psr)) val)
    NIL)

(defun psr-remove-atribuicao! (psr var)
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
    (values
        (reduce
            #'(lambda (acc restr)
                (cond ((null acc) NIL)
                       (T (incf restrcount)
                          (funcall (restricao-funcao-validacao restr) psr))))
            (psr-impl-restricoes psr)
        :initial-value T)
        restrcount)))

; Nota: se uma restricao nao e verificada, entao nao e necessario verificar mais
; nenhuma. E o que e verificado na primeira forma do cond.
(defun psr-variavel-consistente-p (psr var)
    (let ((restrcount 0))
    (values
        (reduce
            #'(lambda (acc restr)
                (cond ((null acc) NIL)
                    (T
                        (incf restrcount)
                        (funcall (restricao-funcao-validacao restr) psr))))
            (psr-variavel-restricoes psr var)
            :initial-value T)
        restrcount)))

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

; Nota: utilizamos a uniao das restricoes das variaveis para evitar verificar
; mais do que uma vez a mesma restricao.
(defun psr-atribuicoes-consistentes-arco-p (psr var1 val1 var2 val2)
    (let ((restrcount 0)
          (oldval1 (psr-variavel-valor psr var1))
          (oldval2 (psr-variavel-valor psr var2))
          (result T))
    (psr-adiciona-atribuicao! psr var1 val1)
    (psr-adiciona-atribuicao! psr var2 val2)

    (setf result
        (reduce
            #'(lambda (acc restr)
                (cond ((null acc) NIL)
                    (T
                        (incf restrcount)
                        (funcall (restricao-funcao-validacao restr) psr))))
            (intersection
                (psr-variavel-restricoes psr var1)
                (psr-variavel-restricoes psr var2))
            :initial-value result))

    (if oldval1
        (psr-adiciona-atribuicao! psr var1 oldval1)
        (psr-remove-atribuicao! psr var1))
    (if oldval2
        (psr-adiciona-atribuicao! psr var2 oldval2)
        (psr-remove-atribuicao! psr var1))

    (values result restrcount)))

; =============================================================================
; = Funcoes de conversao                                                      =
; =============================================================================

(defun fill-a-pix->psr (arr)
    (let ((vars NIL)
          (doms NIL)
          (restrs NIL))
    (dotimes (i (array-dimension arr 0))
    (dotimes (j (array-dimension arr 1))
        (setf vars (cons (variavel-nome (cons i j)) vars)
              doms (cons (list 0 1) doms))
        (let ((elm (aref arr i j))
              (restrFun NIL)
              (restrVars (mapcar #'variavel-nome (matrix-adjacent
                                                    (array-dimension arr 0)
                                                    (array-dimension arr 1)
                                                    i j :self T))))
        (cond
            ((and (numberp elm) (>= elm 0) (<= elm 9))
                (setf restrFun
                    #'(lambda (psr)
                        (let* ((vals (mapcar #'(lambda (var) (psr-variavel-valor psr var)) restrVars))
                               (remAttrs (reduce #'(lambda (acc e) (if (null e) (+ acc 1) acc)) vals :initial-value 0))
                               (sum (reduce #'(lambda (acc e) (if e (+ acc e) acc)) vals :initial-value 0)))
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
            (setf currentRow (cons (psr-variavel-valor psr (variavel-nome (cons i j))) currentRow)))
        (setf rows       (cons (reverse currentRow) rows)
              currentRow NIL))
    (make-array (list l c) :initial-contents (reverse rows))))

; =============================================================================
; = Funcoes de conversao                                                      =
; =============================================================================

(defun procura-retrocesso-simples (psr &optional (count 0))
    (let ((var (car (psr-variaveis-nao-atribuidas psr))))
    (if var
        (let ((dom (psr-variavel-dominio psr var)))
        (dolist (val dom)
            (multiple-value-bind (check cnt) (psr-atribuicao-consistente-p psr var val)
            ;(format T "var: ~A val: ~A chk: ~A~%" var val cnt)
            (incf count cnt)
            (psr-adiciona-atribuicao! psr var val)
            (if check
                (multiple-value-bind (newpsr total) (procura-retrocesso-simples psr count)
                    ;(format T "(R) var: ~A val: ~A chk: ~A~%" var val total)
                    ; Se o PSR nao e NIL, procura encontrou solucao
                    (if newpsr
                        (return-from procura-retrocesso-simples (values newpsr total))
                        (setf count total))))))
        (psr-remove-atribuicao! psr var)
        (return-from procura-retrocesso-simples (values NIL count))))
    (values psr count)))

(defun resolve-simples (arr)
    (psr->fill-a-pix
        (procura-retrocesso-simples (fill-a-pix->psr arr))
        (array-dimension arr 0)
        (array-dimension arr 1)))

(defun resolve-best (arr)
    (resolve-simples (arr)))

; =============================================================================
; = Funcoes auxiliares                                                        =
; =============================================================================

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

(defun variavel-nome (pos)
    (format NIL "(~D,~D)" (car pos) (cdr pos)))

(defun matrix-adjacent (width height line column &key (self NIL))
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

