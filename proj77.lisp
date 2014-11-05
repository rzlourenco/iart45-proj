; Grupo 77
; ist176133 - Rodrigo Lourenco
; ist179515 - Joao Vasco Pestana
; -*- vim: ts=8 sw=2 sts=2 expandtab -*-
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
  (list-find-assoc (psr-impl-variaveis psr) (psr-impl-dominios psr) var))

; Nota: devolve uma copia da lista de restricoes onde todas as restricoes
; devolvidas incluem a variavel especificada.
(defun psr-variavel-restricoes (psr var)
  (remove-if
    #'(lambda (r)
      (not (find var (restricao-variaveis r) :test #'equal)))
    (psr-impl-restricoes psr)))

; Nota: visto que o valor de uma variavel nao definida e NIL, entao vamos
; aproveitar para simplificar algum codigo que faz modificaoes temporarias ao
; permitir que atribuir NIL a uma variavel a apague, sendo desnecessario o teste
; a NIL do valor anterior seguido de uma remocao.
(defun psr-adiciona-atribuicao! (psr var val)
  (cond ((null val)
          (psr-remove-atribuicao! psr var)
          NIL)
        (T
          (setf (gethash var (psr-impl-atribuicoes psr)) val)
          NIL)))

(defun psr-remove-atribuicao! (psr var)
  (remhash var (psr-impl-atribuicoes psr))
  NIL)

(defun psr-altera-dominio! (psr var dom)
  (list-change-assoc (psr-impl-variaveis psr) (psr-impl-dominios psr) var dom)
  NIL)

(defun psr-completo-p (psr)
  (let ((hashcnt (hash-table-count (psr-impl-atribuicoes psr)))
        (numvars (psr-impl-num-vars psr)))
    (equal hashcnt numvars)))

(defun psr-consistente-p (psr)
  (let ((restrcount 0))
    (values
      (every
        #'(lambda (restr)
            (setf restrcount (+ restrcount 1))
            (funcall (restricao-funcao-validacao restr) psr))
        (psr-impl-restricoes psr))
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
                    (setf restrcount (+ restrcount 1))
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
    (psr-adiciona-atribuicao! psr var oldval)
    (values-list ret)))

(defun psr-atribuicoes-consistentes-arco-p (psr var1 val1 var2 val2)
  (error "asdfasd" T)
  (let ((restrcount 0)
        (oldval1 (psr-variavel-valor psr var1))
        (oldval2 (psr-variavel-valor psr var2))
        (result T))
    (psr-adiciona-atribuicao! psr var1 val1)
    (psr-adiciona-atribuicao! psr var2 val2)

    (setf result
      (reduce
        #'(lambda (acc restr)
            (cond (acc NIL)
                  (T
                    (setf restrcount (+ restrcount 1))
                    (funcall (restricao-funcao-validacao restr) psr))))
        (union (psr-variavel-restricoes psr var1)
               (psr-variavel-restricoes psr var2))))

    (psr-adiciona-atribuicao! psr var1 oldval1)
    (psr-adiciona-atribuicao! psr var2 oldval2)
    (values result restrcount)))

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
        (T (list-find-assoc (rest keys) (rest vals) key cmp))))

(defun list-change-assoc (keys vals key newval &optional (cmp #'equal))
  (cond ((or (null keys) (null vals)) NIL)
        ((funcall cmp (first keys) key) (setf (car vals) newval))
        (T (list-change-assoc (rest keys) (rest vals) key newval cmp))))

; Aceita uma hash-table e devolve uma lista de todos os pares (chave valor)
; na tabela.
(defun hash-table-keyvalues (table)
  (let ((lst ()))
    (maphash #'(lambda (k v) (setf lst (cons (cons k v) lst))) table)
    lst))
