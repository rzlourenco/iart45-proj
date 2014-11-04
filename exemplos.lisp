(defparameter *caracter* "#")

;; acrescentei algumas funcoes auxiliares que vao dar jeito para testar automaticamente o codigo dos alunos
(defun ignore-value (x)
	(declare (ignore x))
	'ignore)
	
(defun conjuntos-iguais-p (l1 l2 &key (test #'equal))
	(and (null (set-difference l1 l2 :test test))
		 (null (set-difference l2 l1 :test test))))

;;;desenha-fill-a-pix: array --> {}
;;; recebe um array de duas dimensoes correspondente a uma solucao para um problema fill-a-pix, 
;;; ou seja um array que para cada casa ou tem o valor 0 para indicar que a casa nao deve ser desenhada,
;;; ou tem o valor 1 indicando que a casa deve ser desenhada. Desenha a imagem no ecra.
;;; 
(defun desenha-fill-a-pix (tabuleiro)
	(desenha-linha-exterior tabuleiro)
	(dotimes (linha (array-dimension tabuleiro 0))
		(desenha-linha linha tabuleiro))
	(desenha-linha-exterior tabuleiro))
	
;;; desenha-linha-exterior: array --> {}
;;; recebe um array fill-a-pix e desenha uma linha exterior do array (pode ser a linha superior ou inferior)
;;; com o tamanho correspondente ao tamanho do array.
(defun desenha-linha-exterior (tabuleiro)
	(format T "+-")
	(dotimes (coluna (array-dimension tabuleiro 0))
		(format T "--"))
	(format T "+~%"))
	
;; desenha-linha: array --> {}
;;; recebe um array fill-a-pix e desenha uma das linhas do array no ecra
(defun desenha-linha (linha tabuleiro)
	(format T "| ")
	(dotimes (coluna (array-dimension tabuleiro 0))
		(format T "~A " (if (zerop (aref tabuleiro linha coluna)) " " *caracter*)))
	(format T "|~%"))

;;caso mais simples possivel, uma unica restricao de que tem de ser tudo preto a volta da casa central
(defparameter e0 (make-array (list 3 3) :initial-contents 
	'((NIL NIL NIL)
	  (NIL 9 NIL)
	  (NIL NIL NIL))))

;;este exemplo tem multiplas solucoes possiveis
(defparameter e1 (make-array (list 5 5) :initial-contents
	'((NIL 2 3 NIL NIL)
	  (NIL NIL NIL NIL NIL)
	  (NIL NIL 5 NIL NIL)
	  (NIL 4 NIL 5 NIL)
	  (NIL NIL 4 NIL NIL)
	  )))
	 
	  
(defparameter e1_1 (make-array (list 5 5) :initial-contents
	'((NIL NIL 1 NIL NIL)
	  (NIL 1 NIL NIL 5)
	  (1 NIL NIL NIL 6)
	  (NIL NIL NIL 9 NIL)
	  (NIL 5 6 NIL NIL))))

;; os exemplos seguintes foram retirados dos seguintes sitios:
;; http://www.conceptispuzzles.com/index.aspx?uri=puzzle/fill-a-pix
;; http://www.kongregate.com/games/conceptis/basic-logic-fill-a-pix-light-vol-1
;; se alguma alma caridosa tiver a paciencia para construir uma das tabelas maiores (dos exemplos dos sites)
;; por favor envie-me um email :)
(defparameter e2 (make-array (list 10 10) :initial-contents
	'((NIL 2 3 NIL NIL 0 NIL NIL NIL NIL)
	  (NIL NIL NIL NIL 3 NIL 2 NIL NIL 6)
	  (NIL NIL 5 NIL 5 3 NIL 5 7 4)
	  (NIL 4 NIL 5 NIL 5 NIL 6 NIL 3)
	  (NIL NIL 4 NIL 5 NIL 6 NIL NIL 3)
	  (NIL NIL NIL 2 NIL 5 NIL NIL NIL NIL)
	  (4 NIL 1 NIL NIL NIL 1 1 NIL NIL)
	  (4 NIL 1 NIL NIL NIL 1 NIL 4 NIL)
	  (NIL NIL NIL NIL 6 NIL NIL NIL NIL 4)
	  (NIL 4 4 NIL NIL NIL NIL 4 NIL NIL))))
	  
(defparameter e3 (make-array (list 10 10) :initial-contents
	'((NIL NIL 3 3 NIL NIL NIL NIL NIL NIL)
	  (3 NIL NIL NIL NIL NIL 0 NIL 0 NIL)
	  (NIL NIL 3 4 NIL 3 NIL NIL NIL NIL)
	  (3 NIL 4 NIL NIL NIL NIL 3 NIL NIL)
	  (2 3 NIL 5 NIL 4 4 NIL NIL 4)
	  (NIL NIL 5 4 6 6 NIL 4 NIL 4)
	  (NIL NIL NIL NIL NIL 3 3 NIL NIL 4)
	  (NIL 3 NIL NIL 5 6 5 NIL NIL 4)
	  (NIL NIL NIL 7 NIL NIL NIL 7 NIL 5)
	  (NIL 4 NIL NIL 6 NIL 6 NIL 5 NIL))))
	  
(defparameter e4 (make-array (list 10 10) :initial-contents
	'((3 NIL NIL 2 2 0 2 2 NIL NIL)
	  (4 NIL 6 NIL NIL 1 NIL NIL 6 4)
	  (NIL NIL 6 NIL NIL NIL 5 6 NIL NIL)
	  (NIL NIL NIL NIL 5 5 5 NIL 5 3)
	  (NIL 0 2 4 6 NIL NIL NIL NIL 3)
	  (NIL NIL 3 NIL NIL 2 NIL NIL NIL 2)
	  (NIL 3 NIL NIL 2 NIL NIL 3 NIL NIL)
	  (NIL NIL 3 NIL 3 NIL 3 NIL NIL NIL)
	  (4 NIL NIL NIL 4 3 NIL 3 3 NIL)
	  (NIL 4 NIL 3 NIL NIL 2 NIL NIL NIL))))
	  
(defparameter e5 (make-array (list 15 15) :initial-contents
	'((0 NIL NIL 4 3 2 1 NIL NIL NIL NIL NIL 3 NIL NIL)
	  (NIL NIL 5 NIL NIL 4 NIL NIL 4 4 NIL NIL NIL NIL 3)
	  (NIL 5 4 5 4 5 5 NIL 5 3 NIL 1 2 NIL 3)
	  (4 NIL NIL NIL 4 NIL NIL 4 2 NIL 1 NIL NIL NIL NIL)
	  (NIL NIL 5 4 NIL 2 2 NIL 1 0 NIL NIL 7 5 NIL)
	  (NIL NIL NIL 5 NIL NIL 0 NIL NIL NIL NIL 4 5 NIL 2)
	  (4 NIL NIL 5 4 2 0 0 NIL NIL NIL 5 6 NIL NIL)
	  (5 NIL NIL 6 5 NIL NIL NIL NIL NIL 3 3 3 NIL 3)
	  (NIL NIL 5 NIL 5 3 NIL NIL NIL NIL NIL NIL 3 NIL NIL)
	  (5 NIL NIL 6 5 NIL 3 5 NIL 6 NIL NIL 0 NIL 0)
	  (NIL NIL 5 NIL 4 3 2 4 5 NIL 4 NIL NIL 1 NIL)
	  (NIL 7 NIL NIL 5 NIL NIL 1 NIL 5 5 5 NIL NIL NIL)
	  (NIL NIL 6 4 4 4 3 1 2 4 NIL NIL 6 4 NIL)
	  (NIL 5 NIL 6 NIL NIL NIL NIL NIL 4 6 NIL NIL NIL NIL)
	  (NIL NIL NIL NIL NIL NIL 3 2 0 NIL 4 4 3 NIL 2))))
	  
(defparameter e6 (make-array (list 15 15) :initial-contents
	'((NIL NIL NIL NIL 5 NIL 4 NIL NIL NIL NIL NIL 0 NIL NIL)
	  (NIL 0 NIL NIL NIL 7 NIL NIL NIL 0 NIL NIL NIL 0 NIL)
	  (NIL NIL NIL NIL 6 4 NIL 4 3 NIL NIL NIL 0 NIL NIL)
	  (NIL NIL NIL NIL NIL NIL 4 4 NIL 0 NIL NIL NIL 0 NIL)
	  (NIL 0 NIL NIL NIL NIL 4 3 2 NIL 4 4 NIL NIL 0)
	  (NIL NIL NIL NIL 6 7 5 5 3 NIL 6 NIL 5 NIL NIL)
	  (NIL NIL 3 NIL 8 NIL NIL 4 NIL 6 NIL 6 NIL NIL NIL)
	  (3 NIL NIL NIL NIL 7 NIL NIL 6 6 NIL 5 4 NIL 3)
	  (5 5 NIL NIL 7 5 NIL NIL NIL 5 NIL 5 NIL NIL 4)
	  (NIL NIL 6 NIL 6 5 NIL 6 6 NIL 5 5 NIL 4 NIL)
	  (3 5 NIL 4 4 NIL 4 NIL NIL NIL NIL NIL 2 NIL 2)
	  (NIL NIL NIL NIL NIL 6 6 NIL NIL NIL NIL 3 NIL NIL NIL)
	  (3 NIL NIL 5 4 NIL 4 5 4 6 3 NIL 3 NIL NIL)
	  (NIL 7 6 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL 2)
	  (NIL NIL 5 NIL NIL 4 NIL 4 NIL 5 NIL 5 NIL NIL NIL))))
	  
;; depois deste ja nao tive paciencia para mais...
(defparameter e7 (make-array (list 20 20) :initial-contents
	'((4 NIL NIL 6 NIL NIL NIL 6 NIL NIL 4 NIL 4 NIL NIL 1 NIL NIL 3 NIL)
	  (NIL NIL 9 NIL 8 NIL 9 8 NIL NIL NIL NIL NIL 2 2 NIL 6 NIL NIL 3)
	  (6 NIL NIL NIL NIL 7 7 NIL NIL 2 NIL 1 2 NIL 2 4 6 8 NIL 4)
	  (5 NIL NIL NIL 3 NIL NIL NIL 3 NIL NIL NIL 0 NIL NIL NIL NIL NIL 7 NIL)
	  (NIL NIL 1 NIL NIL NIL NIL NIL NIL 0 NIL NIL NIL NIL NIL NIL 5 5 NIL 4)
	  (NIL NIL NIL NIL NIL 0 NIL NIL 1 NIL NIL NIL NIL NIL NIL 4 NIL 6 NIL 4)
	  (NIL 0 NIL NIL NIL 3 NIL NIL 3 NIL 2 NIL 2 NIL 1 3 4 NIL NIL NIL)
	  (NIL NIL NIL 6 NIL NIL NIL NIL 3 4 NIL NIL 5 NIL NIL NIL 6 NIL NIL NIL)
	  (0 NIL NIL 8 NIL NIL 3 NIL 4 NIL 6 8 6 NIL NIL NIL NIL 8 NIL 3)
	  (NIL NIL NIL NIL 6 4 NIL 2 3 NIL NIL NIL NIL 7 6 NIL 7 9 NIL NIL)
	  (NIL NIL NIL NIL NIL 5 NIL NIL NIL 5 NIL 6 7 NIL NIL NIL 5 7 NIL NIL)
	  (NIL 7 8 NIL 8 NIL NIL NIL NIL NIL 4 NIL NIL 6 NIL NIL NIL 6 NIL NIL)
	  (NIL NIL NIL 7 NIL NIL 7 NIL NIL 5 NIL NIL NIL NIL NIL 1 NIL NIL 6 NIL)
	  (5 NIL NIL NIL NIL NIL NIL NIL 3 3 NIL 6 NIL NIL 5 NIL NIL NIL NIL NIL)
	  (NIL NIl 7 NIL 7 NIL NIL NIL 5 NIL NIL NIL 7 NIL 3 NIL 3 NIL NIL 5)
	  (NIL 5 NIL 7 NIL NIL NIL 1 NIL 1 NIL NIL 7 NIL NIL NIL NIL NIL NIL NIL)
	  (NIL 5 NIL NIL NIL 4 5 NIL NIL NIL NIL NIL NIL NIL 1 NIL 2 5 NIL 3)
	  (NIL 7 9 NIL 8 NIL NIL 1 NIL NIL NIL NIL 7 NIL NIL 6 NIL NIL 5 NIL)
	  (NIL 5 NIL 7 NIL NIL NIL NIL NIL 5 NIL NIL NIL NIL 3 NIL NIL NIL NIL 3)
	  (NIL NIL NIL NIL 6 5 NIL NIL 4 5 5 NIL NIL 3 NIL NIL NIL 3 NIL NIL))))