
(assert
    (not
        (=> 
            (= 
                (ControlFlow 0 0) 8) 
            (let 
                (
                    ($generated@@101  
                        (and 
                            (=> 
                                (= 
                                    (ControlFlow 0 2) 
                                    (- 0 4)) assert12 ) 
                            (and 
                                (=> 
                                    (= 
                                        (ControlFlow 0 2) 
                                        (- 0 3))  
                                    (and 
                                        assertId8
                                        (=> 
                                            (>= x 0) 
                                            (=  x y)))) 
                                (=> 
                                    (=> 
                                        (>= x 0) 
                                        (= x y)) 
                                    (=> 
                                        (= 
                                            (ControlFlow 0 2) 
                                            (- 0 1))  
                                        (and assert9 
                                            (=> 
                                                (< x 0) 
                                                (= 
                                                    (+ x y) 0)))))))))
                (let 
                    (
                        # Obrigations for the else branch 
                        ($generated@@102  
                            (=> 
                                (<= 0 x ) 
                                (=> 
                                    (and 
                                        (= y x) 
                                        (= 
                                            (ControlFlow 0 6) 2)) $generated@@101))))
                    (let 
                        (
                            # Obrigations for the main brnach where y = -x 
                            ($generated@@103  
                                (=> 
                                    (and 
                                        (and 
                                            (< x  0)  
                                            // This 03 is the assume statement (id10)
                                            // Aqui esta a diferenca aqui isto generate 93 da uma ssuncao que e devolvida
                                            // pelo SMT como essencial 

                                            // If 93 active the equality that one olds 
                                            // if 93 not active that equality y=-x does not old 
                                            //$generated@@93 is a predicate used as a pre-condition or witness for that 
                                            //equality — typically it means “it is valid to use $generated@@94 here” or it comes 
                                            //from a let/fresh binding that ensured the equality. Often this is a trivial
                                            // generated guard (e.g. proof that the RHS was well-formed).
                                            // Aqui esta o gato 'e por causa disto que esta linha 'e highlighted
                                            (=> $generated@@93 
                                                (= $generated@@94 
                                                    (- 0  x)))) 
                                        (and 
                                            (= y $generated@@94) 
                                            (= 
                                                (ControlFlow 0 5) 2))) $generated@@101)))
                        (let 
                            (
                                ($generated@@104  
                                    (=> 
                                        // Frame predicates i guess ! (not used in this )
                                        // Composed formula from larger blocks Wp formula 
                                        (= $generated@@95 
                                            //(declare-fun $generated@@29 (T@U T@U T@U Bool) T@U) 1 ref
                                            //(declare-fun $generated@@96 () T@U) 1 ref 
                                            //(declare-fun $generated@@97 () T@U)
                                            //(declare-fun $generated@@98 () T@U)
                                            //(declare-sort |T@U| 0)
                                            // I do not underanded this generated 95 at all 
                                            ($generated@@29 $generated@@96 $generated@@97 $generated@@98 false)) 
                                        (and 
                                            // Code call of each branch 
                                            (=> 
                                                (= 
                                                    // Stated the branch of the if control flow
                                                    (ControlFlow 0 7) 5) $generated@@103) 
                                            (=> 
                                                (= 
                                                    // Stated the branch of the else control flow 
                                                    (ControlFlow 0 7) 6) $generated@@102)))))
                            (let 
                                (
                                    ($generated@@105  
                                    // Ties everything , 104 the code, the 99 07 etc frame checks
                                  
                                        (=> 
                                            (and 
                                                (and 
                                                    ($generated@@99 $generated@@97) 
                                                    ($generated@@100 $generated@@97)) 
                                                (= 
                                                    (ControlFlow 0 8) 7)) $generated@@104)))
$generated@@105))))))
))
