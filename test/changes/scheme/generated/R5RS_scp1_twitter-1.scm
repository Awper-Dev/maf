; Changes:
; * removed: 2
; * added: 3
; * swaps: 4
; * negated predicates: 1
; * swapped branches: 0
; * calls to id fun: 3
(letrec ((result ())
         (output (lambda (i)
                   (set! result (cons i result))))
         (linebreak (lambda ()
                      (set! result (cons 'linebreak result))))
         (output-all (lambda args
                       (for-each output args)))
         (output-all-sep (lambda (args)
                           (for-each (lambda (arg) (output arg) (output " ")) args)))
         (make-tweet (lambda (username text tags)
                       (letrec ((output-tweet (lambda ()
                                                (output-all "Tweet from " username "\n" text "\nTags: ")
                                                (<change>
                                                   (output-all-sep tags)
                                                   ())
                                                (linebreak)))
                                (dispatch (lambda (msg)
                                            (if (eq? msg 'text)
                                               text
                                               (if (eq? msg 'tags)
                                                  tags
                                                  (if (eq? msg 'username)
                                                     username
                                                     (if (eq? msg 'output)
                                                        output-tweet
                                                        (begin
                                                           (output "error - wrong msg ")
                                                           (output msg)))))))))
                          (if (> (string-length text) 140) #f dispatch))))
         (make-account (lambda (name username)
                         (let ((followers ())
                               (tweets ())
                               (tweet-wall ()))
                            (letrec ((follow (lambda (account)
                                               ((account 'add-follower) dispatch)))
                                     (add-follower (lambda (account)
                                                     (set! followers (cons account followers))))
                                     (tweet (lambda (text . tags)
                                              (let ((tweet-obj (make-tweet username text tags)))
                                                 (<change>
                                                    (set! tweets (cons tweet-obj tweets))
                                                    ())
                                                 (set! tweet-wall (cons tweet-obj tweet-wall))
                                                 (for-each (lambda (follower) ((follower 'add-tweet-to-wall) tweet-obj)) followers))))
                                     (add-tweet-to-wall (lambda (tweet)
                                                          (set! tweet-wall (cons tweet tweet-wall))))
                                     (output-account (lambda (symbol)
                                                       (if (eq? symbol 'wall)
                                                          (output-wall)
                                                          (if (eq? symbol 'followers)
                                                             (output-followers)
                                                             (if (eq? symbol 'account)
                                                                (output-entire-account)
                                                                (output "wrong symbol given"))))))
                                     (output-wall (lambda ()
                                                    (output "TWEET WALL")
                                                    (<change>
                                                       (linebreak)
                                                       (for-each (lambda (tweet) ((tweet 'output)) (linebreak)) tweet-wall))
                                                    (<change>
                                                       (for-each (lambda (tweet) ((tweet 'output)) (linebreak)) tweet-wall)
                                                       (linebreak))))
                                     (output-followers (lambda ()
                                                         (<change>
                                                            (output "FOLLOWERS")
                                                            (linebreak))
                                                         (<change>
                                                            (linebreak)
                                                            (output "FOLLOWERS"))
                                                         (<change>
                                                            ()
                                                            (display (output " ")))
                                                         (for-each (lambda (follower) (output (follower 'username)) (output " ")) followers)))
                                     (output-entire-account (lambda ()
                                                              (<change>
                                                                 (output-all "Twitter name " username "\n" "Name " name "\n")
                                                                 ((lambda (x) x) (output-all "Twitter name " username "\n" "Name " name "\n")))
                                                              (<change>
                                                                 ()
                                                                 (display output-wall))
                                                              (output-wall)
                                                              (<change>
                                                                 (output-followers)
                                                                 (linebreak))
                                                              (<change>
                                                                 (linebreak)
                                                                 (output-followers))
                                                              (linebreak)))
                                     (dispatch (lambda (msg)
                                                 (if (eq? msg 'name)
                                                    name
                                                    (if (<change> (eq? msg 'username) (not (eq? msg 'username)))
                                                       username
                                                       (if (eq? msg 'output)
                                                          output-account
                                                          (if (eq? msg 'follow)
                                                             follow
                                                             (if (eq? msg 'add-follower)
                                                                add-follower
                                                                (if (eq? msg 'tweet)
                                                                   tweet
                                                                   (if (eq? msg 'add-tweet-to-wall)
                                                                      add-tweet-to-wall
                                                                      (begin
                                                                         (<change>
                                                                            (output "error - wrong msg ")
                                                                            (output msg))
                                                                         (<change>
                                                                            (output msg)
                                                                            (output "error - wrong msg ")))))))))))))
                               dispatch))))
         (my-tweet (make-tweet "madewael" "Racket is cool!" (list "#Racket" "#Scheme")))
         (res1 (equal? (my-tweet 'username) "madewael")))
   ((my-tweet 'output))
   (letrec ((accountE (make-account "Eline Philips" "ephilips"))
            (accountM (make-account "Mattias De Wael" "madewael")))
      (<change>
         ((accountE 'follow) accountM)
         ((lambda (x) x) ((accountE 'follow) accountM)))
      (<change>
         ()
         " ")
      ((accountM 'tweet) "Racket is cool!" "#Racket" "#Scheme")
      ((accountE 'tweet) "Hello World!")
      ((accountE 'output) 'account)
      (<change>
         ((accountM 'output) 'account)
         ((lambda (x) x) ((accountM 'output) 'account)))
      (if res1
         (equal?
            result
            (__toplevel_cons
               'linebreak
               (__toplevel_cons
                  'linebreak
                  (__toplevel_cons
                     " "
                     (__toplevel_cons
                        "ephilips"
                        (__toplevel_cons
                           'linebreak
                           (__toplevel_cons
                              "FOLLOWERS"
                              (__toplevel_cons
                                 'linebreak
                                 (__toplevel_cons
                                    'linebreak
                                    (__toplevel_cons
                                       " "
                                       (__toplevel_cons
                                          "#Scheme"
                                          (__toplevel_cons
                                             " "
                                             (__toplevel_cons
                                                "#Racket"
                                                (__toplevel_cons
                                                   "\nTags: "
                                                   (__toplevel_cons
                                                      "Racket is cool!"
                                                      (__toplevel_cons
                                                         "\n"
                                                         (__toplevel_cons
                                                            "madewael"
                                                            (__toplevel_cons
                                                               "Tweet from "
                                                               (__toplevel_cons
                                                                  'linebreak
                                                                  (__toplevel_cons
                                                                     "TWEET WALL"
                                                                     (__toplevel_cons
                                                                        "\n"
                                                                        (__toplevel_cons
                                                                           "Mattias De Wael"
                                                                           (__toplevel_cons
                                                                              "Name "
                                                                              (__toplevel_cons
                                                                                 "\n"
                                                                                 (__toplevel_cons
                                                                                    "madewael"
                                                                                    (__toplevel_cons
                                                                                       "Twitter name "
                                                                                       (__toplevel_cons
                                                                                          'linebreak
                                                                                          (__toplevel_cons
                                                                                             'linebreak
                                                                                             (__toplevel_cons
                                                                                                'linebreak
                                                                                                (__toplevel_cons
                                                                                                   "FOLLOWERS"
                                                                                                   (__toplevel_cons
                                                                                                      'linebreak
                                                                                                      (__toplevel_cons
                                                                                                         'linebreak
                                                                                                         (__toplevel_cons
                                                                                                            " "
                                                                                                            (__toplevel_cons
                                                                                                               "#Scheme"
                                                                                                               (__toplevel_cons
                                                                                                                  " "
                                                                                                                  (__toplevel_cons
                                                                                                                     "#Racket"
                                                                                                                     (__toplevel_cons
                                                                                                                        "\nTags: "
                                                                                                                        (__toplevel_cons
                                                                                                                           "Racket is cool!"
                                                                                                                           (__toplevel_cons
                                                                                                                              "\n"
                                                                                                                              (__toplevel_cons
                                                                                                                                 "madewael"
                                                                                                                                 (__toplevel_cons
                                                                                                                                    "Tweet from "
                                                                                                                                    (__toplevel_cons
                                                                                                                                       'linebreak
                                                                                                                                       (__toplevel_cons
                                                                                                                                          'linebreak
                                                                                                                                          (__toplevel_cons
                                                                                                                                             "\nTags: "
                                                                                                                                             (__toplevel_cons
                                                                                                                                                "Hello World!"
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   "\n"
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      "ephilips"
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         "Tweet from "
                                                                                                                                                         (__toplevel_cons
                                                                                                                                                            'linebreak
                                                                                                                                                            (__toplevel_cons
                                                                                                                                                               "TWEET WALL"
                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                  "\n"
                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                     "Eline Philips"
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        "Name "
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           "\n"
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              "ephilips"
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 "Twitter name "
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    'linebreak
                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                       " "
                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                          "#Scheme"
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             " "
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                "#Racket"
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   "\nTags: "
                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                      "Racket is cool!"
                                                                                                                                                                                                      (__toplevel_cons "\n" (__toplevel_cons "madewael" (__toplevel_cons "Tweet from " ()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         #f)))