; Grupo 77
; ist176133 - Rodrigo Lourenco
; ist179515 - Joao Vasco Pestana

; =============================================================================
; = Restricao                                                                 =
; =============================================================================

; Restricao: uma de lista de variaveis e um predicado que verifica um psr
(defstruct restricao-impl
  (variaveis NIL)
  (funcao-validacao #'(lambda (psr) (declare (ignore psr)) NIL)))

(defun cria-restricao (vars p)
  (make-restricao-impl :variaveis vars :funcao-validacao p))

(defun restricao-variaveis (r)
  (restricao-impl-variaveis r))

(defun restricao-funcao-validacao (r)
  (restricao-impl-funcao-validacao r))

; =============================================================================
; = PSR                                                                       =
; =============================================================================

; PSR: um problema de satisfacao de restricoes
; TODO novo campo com associacao variavel->dominio?
(defstruct psr-impl
  (variaveis NIL)
  (num-vars 0)
  (dominios NIL)
  (restricoes NIL)
  (atribuicoes (make-hash-table :test #'equal)))

(defun cria-psr (vars doms rests)
  (make-psr-impl :variaveis vars :num-vars (list-length vars) :dominios doms :restricoes rests))

(defun psr-atribuicoes (psr)
  (hash-table-keyvalues (psr-impl-atribuicoes psr)))

(defun psr-variaveis-todas (psr)
  (psr-impl-variaveis psr))

(defun psr-variaveis-nao-atribuidas (psr)
  (remove-if #'(lambda (v) (psr-variavel-valor psr v)) (psr-variaveis-todas psr)))

(defun psr-variavel-valor (psr var)
  (multiple-value-bind (v found)
    (gethash var (psr-impl-atribuicoes psr))
    (declare (ignore found))
    v))

(defun psr-variavel-dominio (psr var)
  (list-find-assoc (psr-impl-variaveis psr) (psr-impl-dominios psr) var))

(defun psr-variavel-restricoes (psr var)
  (remove-if #'(lambda (r) (find var (restricao-variaveis r))) (psr-impl-restricoes psr)))

(defun psr-adiciona-atribuicao! (psr var val)
  (setf (gethash var (psr-impl-atribuicoes psr)) val))

(defun psr-remove-atribuicao! (psr var)
  (remhash var (psr-impl-atribuicoes psr)))

; TODO
(defun psr-altera-dominio! (psr var dom)
  (declare (ignore psr var dom))
  (error "psr-altera-dominio! is undefined!" T))

(defun psr-completo-p (psr)
  (let ((hashcnt (hash-table-count (psr-impl-atribuicoes psr)))
        (numvars (psr-impl-num-vars psr)))
    (equal hashcnt numvars)))

; TODO
(defun psr-consistente-p (psr)
  (declare (ignore psr var))
  (error "psr-consistente-p is undefined!" T))

; TODO
(defun psr-variavel-consistente-p (psr var)
  (declare (ignore psr var))
  (error "psr-variavel-consistente-p is undefined!" T))

; TODO
(defun psr-atribuicao-consistente-p (psr var val)
  (declare (ignore psr var val))
  (error "psr-atribuicao-consistente-p is undefined!" T))

; TODO
(defun psr-atribuicoes-consistentes-arco-p (psr var1 val1 var2 val2)
  (declare (ignore psr var1 val1 var2 val2))
  (error "psr-atribuicoes-consistentes-arco-p is undefined!" T))

; =============================================================================
; = Funcoes de conversao                                                      =
; =============================================================================

; TODO
(defun fill-a-pix->psr (arr)
  (declare (ignore arr))
  (error "fill-a-pix->psr is undefined!" T))

; TODO
(defun psr->fill-a-pix (psr l c)
  (declare (ignore psr l c))
  (error "psr->fill-a-pix is undefined!" T))

; =============================================================================
; = Funcoes de conversao                                                      =
; =============================================================================

; TODO
(defun procura-retrocesso-simples (psr)
  (declare (ignore psr))
  (error "procura-retrocesso-simples is undefined!" T))

; TODO
(defun resolve-simples (arr)
  (declare (ignore arr))
  (error "resolve-simples is undefined!" T))

; =============================================================================
; = Funcoes auxiliares                                                        =
; =============================================================================

; Aceita uma lista de chaves, uma lista de valores e uma chave e devolve o
; valor correspondente a chave. Considera-se que o mapeamento e definido pela
; posicao nas listas.
(defun list-find-assoc (keys vals key &optional (cmp #'equal))
  (cond ((or (null keys) (null vals)) NIL)
        ((funcall cmp (first keys) key) (first vals))
        (T (list-find-assoc (rest keys) (rest vals) key))))

; Aceita uma hash-table e devolve uma lista de todos os pares (chave valor)
; na tabela.
(defun hash-table-keyvalues (table)
  (let ((lst ()))
    (maphash #'(lambda (k v) (setf lst (cons (list k v) lst))) table)
    lst))

