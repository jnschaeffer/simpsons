(use-modules
 (ice-9 format)
 (srfi srfi-1)
 (srfi srfi-69))

(define debug #f)

(define (make-agent name programs)
  (let ((state 'undefined)
	(location 'undefined)
	(current-program (car programs)))
    (lambda (msg)
      (cond ((eq? msg 'name) name)
	    ((eq? msg 'state) state)
	    ((eq? msg 'location) location)
	    ((eq? msg 'programs) programs)
	    ((eq? msg 'current-program) current-program)
	    ((eq? msg 'set-current-program!)
	     (lambda (new-program)
	       (set! current-program new-program)))
	    ((eq? msg 'set-state!)
	     (lambda (new-state)
	       (set! state new-state)))
	    ((eq? msg 'set-location!)
	     (lambda (new-location)
	       (set! location new-location)))
	    (else (error "agent - unknown message" msg))))))

(define (find-matching-program world programs)
  (if (null? programs)
      #f
      (let ((program (car programs))
	    (rest (cdr programs)))
	(if ((program 'predicates-match?) world)
	    program
	    (find-matching-program world (cdr programs))))))

(define (set-program! agent current-program new-program)
  (if (new-program 'is-aside?)
	(begin
	  (format debug "new program is aside\n")
	  ((new-program 'set-next!)
	   (lambda ()
	     (format debug "returning to old program ~a\n" (current-program 'label))
	     ((new-program 'reset!))
	     ((agent 'set-current-program!) current-program))))
	((current-program 'reset!)))

  ((agent 'set-current-program!) new-program))

(define (update-program! world agent)
  (let ((name (agent 'name))
	(matching-program (find-matching-program world (agent 'programs)))
	(current-program (agent 'current-program)))
    (if matching-program
	(if (not (eq? (current-program 'label) (matching-program 'label)))
	    (begin
	      (format debug "~a: switching program from ~a to ~a!\n"
		      name (current-program 'label) (matching-program 'label))
	      (set-program! agent current-program matching-program))
	    (format debug "~a: current program same as matching program\n" name))
	(format debug "~a: no matching program found\n" name))))

(define (update-programs! world)
  (let ((agents (world 'agents)))
    (for-each (lambda (agent) (update-program! world agent))
	      (hash-table-values agents))))

(define (make-world)
  (let* ((agents (make-hash-table))
	 (add-agent!
	  (lambda (agent)
	    (hash-table-set! agents (agent 'name) agent)))
	 (agent-exists?
	  (lambda (name)
	    (hash-table-exists? agents name)))
	 (lookup-agent
	  (lambda (name)
	    (hash-table-ref agents name
			    (lambda () (error "unknown agent" name)))))
	 (set-agent-state!
	  (lambda (name new-state)
	    (let ((agent (lookup-agent name)))
	      ((agent 'set-state!) new-state))))
	 (set-agent-location!
	  (lambda (name new-location)
	    (let ((agent (lookup-agent name)))
	      ((agent 'set-location!) new-location))))
	 (event-stack '())
	 (push-event!
	  (lambda (event)
	    (set! event-stack (cons event event-stack))))
	 (pop-event!
	  (lambda ()
	    (if (null? event-stack)
		#f
		(begin
		  (let ((event (car event-stack)))
		    (set! event-stack (cdr event-stack))
		    event))))))
    (lambda (msg)
      (cond ((eq? msg 'agents) agents)
	    ((eq? msg 'agent-exists?) agent-exists?)
	    ((eq? msg 'lookup-agent) lookup-agent)
	    ((eq? msg 'add-agent!) add-agent!)
	    ((eq? msg 'set-agent-state!) set-agent-state!)
	    ((eq? msg 'set-agent-location!) set-agent-location!)
	    ((eq? msg 'push-event!) push-event!)
	    ((eq? msg 'pop-event!) pop-event!)
	    (else (error "world - unknown message" msg))))))

(define (make-set-state! acting-name recipient-name new-state)
  (lambda (world)
    (let ((_ ((world 'lookup-agent) acting-name)))
      ((world 'set-agent-state!) recipient-name new-state)
      ((world 'push-event!)
       (lambda ()
	 (format #t "~a: ~a is ~a\n" acting-name recipient-name new-state))))))

(define (make-set-location! acting-name recipient-name new-location)
  (lambda (world)
    (let ((_ ((world 'lookup-agent) acting-name)))
      ((world 'set-agent-location!) recipient-name new-location)
      ((world 'push-event!)
       (lambda ()
	 (format #t "~a: ~a is at ~a\n" acting-name recipient-name new-location))))))

(define (make-test test? then-op else-op)
  (lambda (world)
    (if (test? world)
	(then-op world)
	(else-op world))))

(define (make-say agent-name msg)
  (lambda (world)
    (let ((agent ((world 'lookup-agent) agent-name)))
      (format #t "~a: ~s\n" agent-name msg))))

(define (make-noop agent-name)
  (lambda (world)
    (let ((agent ((world 'lookup-agent) agent-name)))
      (format debug "~a: ...\n" agent-name))))

(define (make-state-pred name target-state)
  (lambda (world)
    (let* ((agent ((world 'lookup-agent) name))
	   (state (agent 'state)))
      (if (eq? state target-state)
	  (begin
	    (format #f "(world) ~a is currently ~a\n" name state)
	    #t)
	  #f))))

(define (make-location-pred name target-location)
  (lambda (world)
    (let* ((agent ((world 'lookup-agent) name))
	   (location (agent 'location)))
      (if (eq? location target-location)
	  (begin
	    (format #f "(world) ~a is currently at ~a\n" name location)
	    #t)
	  #f))))

(define (make-random-pred probability)
  (lambda (world)
    (let ((p (random 1.0)))
      (format debug "p is ~a, must be less than ~a\n" p probability)
      (< p probability))))

(define (make-program label is-aside? next predicates ops)
  (let* ((pc ops)
	 (reset!
	  (lambda ()
	    (format debug "resetting ~a!\n" label)
	    (set! pc ops)
	    (set! next (lambda () (error "program - no next program")))))
	 (step!
	  (lambda (world)
	    (let ((op (car pc))
		  (next-ops (cdr pc)))
	      (op world)
	      (if (null? next-ops)
		  (if is-aside?
		      (next)
		      (begin
			(format debug "~a: pc null - rewinding\n" label)
			(reset!)))
		  (set! pc next-ops)))))
	 (predicates-match?
	  (lambda (world)
	    (fold
	     (lambda (pred current) (if current (pred world) #f))
	     #t
	     predicates))))
    (lambda (msg)
      (cond ((eq? msg 'reset!) reset!)
	    ((eq? msg 'step!) step!)
	    ((eq? msg 'is-aside?) is-aside?)
	    ((eq? msg 'predicates-match?) predicates-match?)
	    ((eq? msg 'label) label)
	    ((eq? msg 'next) next)
	    ((eq? msg 'set-next!)
	     (lambda (new-next)
	       (set! next new-next)))
	    (else (error "program - unknown message" msg))))))

(define (world-render-events! world)
  (let ((event ((world 'pop-event!))))
    (if event
	(begin
	  (event)
	  (world-render-events! world))
	#f)))

(define (agent-step! world agent)
  (let ((program (agent 'current-program)))
    ((program 'step!) world)))

(define (world-step! world)
  (let* ((agent-table (world 'agents))
	 (agents (hash-table-values agent-table)))
    (world-render-events! world)
    (for-each (lambda (agent) (agent-step! world agent)) agents)
    (for-each (lambda (agent) (update-program! world agent)) agents)))

(define-syntax predicate
  (syntax-rules (not state location rand any)
    ((_ (not p))
     (lambda (world)
       (not ((predicate p) world))))
    ((_ (state name test-state))
     (make-state-pred (quote name) (quote test-state)))
    ((_ (location name test-location))
     (make-location-pred (quote name) (quote test-location)))
    ((_ (rand probability))
     (make-random-pred probability))
    ((_ any)
     (lambda (world) #t))))

(define-syntax operation
  (syntax-rules (set-state! set-location! test say block no-op)
    ((_ agent-name (set-state! name target-state))
     (make-set-state! (quote agent-name) (quote name) (quote target-state)))
    ((_ agent-name (set-location! name target-location))
     (make-set-location! (quote agent-name) (quote name) (quote target-location)))
    ((_ agent-name (test condition then-op else-op))
     (make-test (predicate condition) (operation agent-name then-op) (operation agent-name else-op)))
    ((_ agent-name (block o ...))
     (lambda (world)
       (for-each
	(lambda (op)
	  (op world))
	(list
	 (operation agent-name o)
	 ...))))
    ((_ agent-name (say msg))
     (make-say (quote agent-name) msg))
    ((_ agent-name (no-op))
     (make-noop (quote agent-name)))))

(define-syntax build-program  
  (syntax-rules (program aside conditions operations)
    ((_ agent-name (program name (conditions c ...) (operations o ...)))
     (make-program
      (quote name)
      #f
      (lambda () (error "no next program"))
      (list (predicate c) ...)
      (list (operation agent-name o) ...)))
    ((_ agent-name (aside name (conditions c ...) (operations o ...)))
     (make-program
      (quote name)
      #t
      (lambda () (error "no next program"))
      (list (predicate c) ...)
      (list (operation agent-name o) ...)))))

(define-syntax programs
  (syntax-rules ()
    ((_ name p ...)
     (list
      (build-program name p)
      ...))))

(define-syntax agent
  (syntax-rules (programs)
    ((_ name (programs p ...))
     (make-agent
      (quote name)
      (programs
       name
       p
       ...)))))

; everyone sits in the living room in silence. maggie crawls between rooms.
; the TV turns on whenever she walks in.
(define tv
  (agent tv
	 (programs
	  (program start
		   (conditions
		    (state tv undefined))
		   (operations
		    (block
		     (set-location! tv living-room)
		     (set-state! tv off))))
	  (aside maggie-is-here
		 (conditions
		  (not (state tv on))
		  (location maggie living-room))
		 (operations
		  (block
		   (say "maggie is here now")
		   (set-state! tv on))))
	  (program on
		   (conditions
		    (state tv on))
		   (operations
		    (block
		     (say "i am playing itchy and scratchy"))))
	  (program off
		   (conditions
		    (state tv off))
		   (operations
		    (no-op))))))

(define maggie
  (agent maggie
	 (programs
	  (program start
		   (conditions any)
		   (operations
		    (set-location! maggie maggies-room)
		    (say "this is my room")
		    (set-location! maggie stairs)
		    (no-op)
		    (set-location! maggie living-room)
		    (set-location! maggie kitchen)
		    (no-op)
		    (say "the kitchen is warm")
		    (set-location! maggie dining-room)
		    (set-location! maggie living-room)
		    (set-location! maggie stairs))))))

(define marge
  (agent marge
	 (programs
	  (program start
		   (conditions
		    (state marge undefined))
		   (operations
		    (block
		     (set-location! marge living-room)
		     (set-state! marge sitting))))
	  (aside maggie-is-here
		 (conditions
		  (location maggie living-room))
		 (operations
		  (say "maggie is here now")))
	  (aside hate-tv
		 (conditions
		  (state tv on))
		 (operations
		   (block (say "i hate tv")
			  (set-state! tv off))))
	  (program sitting
		   (conditions any)
		   (operations
		    (no-op))))))

(define bart
  (agent bart
	 (programs
	  (program start
		   (conditions
		    (state bart undefined))
		   (operations
		    (block
		     (set-location! bart living-room)
		     (set-state! bart sitting))))
	  (aside maggie-is-here
		 (conditions
		  (location maggie living-room))
		 (operations
		  (say "maggie is here now")))
	  (aside choking-bart
		 (conditions
		  (state homer choking-bart))
		 (operations
		  (say "don't have a cow, man")))
	  (aside love-tv
		 (conditions
		  (state tv on))
		 (operations
		   (say "i love tv")))
	  (program sitting
		   (conditions any)
		   (operations
		    (no-op))))))
(define apu
  (agent apu
	 (programs
	  (program start
		   (conditions
		    (state apu undefined))
		   (operations
		    (block
		     (set-location! apu kwik-e-mart)
		     (set-state! apu waiting))))
	  (aside homer-is-here
		   (conditions
		     (rand 0.2)
		     (location homer kwik-e-mart))
		    (operations
		     (block
		      (say "homer, not here")
		      (set-location! homer outside)
		      (set-state! homer leaving))))
	  (program waiting
		   (conditions
		    (state apu waiting)
		    (not (location homer kwik-e-mart)))
		   (operations
		    (no-op))))))

(define homer
  (agent homer
	 (programs
	  (program start
		   (conditions
		    (state homer undefined))
		   (operations
		    (block
		     (set-location! homer living-room)
		     (set-state! homer sitting))))
	  (program go-home
		   (conditions
		    (state homer leaving))
		   (operations
		    (say "okay")
		    (block
		     (set-location! homer beyond)
		     (set-state! homer wandering))))
	  (program home-now
		   (conditions
		    (rand 0.1)
		    (state homer wandering))
		   (operations
		    (block
		     (set-location! homer living-room)
		     (set-state! homer sitting)
		     (say "i can go home now"))))
	  (program wandering
		   (conditions
		    (state homer wandering))
		   (operations
		    (set-state! homer wandering)))
	  (program please-donut
		   (conditions
		    (location homer kwik-e-mart))
		   (operations
		    (say "please give donut")))
	  (program seeking-donut
		   (conditions
		    (state homer want-donut))
		   (operations
		    (say "homer's journey")
		    (set-location! homer homercar)
		    (set-location! homer street)
		    (set-location! homer kwik-e-mart)))
	  (aside choking-bart
		 (conditions
		  (rand 0.2)
		  (state homer sitting)
		  (location homer living-room))
		 (operations
		  (set-state! homer choking-bart)
		  (set-state! homer sitting)))
	  (aside homers-journey
		 (conditions
		  (rand 0.1)
		  (state homer sitting)
		  (location homer living-room))
		 (operations
		  (set-state! homer want-donut)))
	  (program sitting
		   (conditions
		    (state homer sitting))
		   (operations
		    (no-op))))))
