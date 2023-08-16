namespace Hol.Tests

open FsUnit.Xunit
open Xunit

open HOL
open System

module DLTreeTests =

    [<Fact>]
    let ``dltree_empty_test``() =
        dltree_empty
        |> should equal Leaf

    [<Fact>]
    let ``dltree_elems_test``() =

        (*           D[3]          *)
        (*          /    \         *)
        (*        B[2]  E[2]       *)
        (*       /   \             *)
        (*    A[1]   C[1]          *)

        dltree_elems (Node (3,("D",""),Node (2,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))
        |> should equal [("A", ""); ("B", ""); ("C", ""); ("D", ""); ("E", "")]

    [<Fact>]
    let ``level_leaf_test``() =
        level Leaf
        |> should equal 0

    [<Fact>]
    let ``level_node_test``() =

        level (Node (3,("D",""),Node (2,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))
        |> should equal 3

    (* level tests *)

    [<Fact>]
    let ``rightmost_elem_leaf_test``() =

        rightmost_elem ("C","") Leaf
        |> should equal ("C","")

    [<Fact>]
    let ``rightmost_elem_node_test``() =

        rightmost_elem ("C","") (Node (3,("D",""),Node (2,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))
        |> should equal ("E","")

    (* right_app tests *)

    let func1 tr = 
            match tr with
            | Leaf -> Leaf
            | Node (i, xy, tr1, tr2) -> Node (i, xy, tr2, tr1)

    [<Fact>]
    let ``right_app_test``() =

        (*       D[3]            -->       D[3]              *)
        (*      /    \           -->      /    \             *)
        (*    E[2]    B[2]       -->    E[2]    B[2]         *)   
        (*            /   \      -->            /   \        *)   
        (*         A[1]   C[1]   -->         C[1]   A[1]     *)

        let aNode = Node (1,("A",""),Leaf,Leaf)
        let cNode = Node (1,("C",""),Leaf,Leaf)
        let eNode = Node (2,("E",""),Leaf,Leaf)

        let expected = (Node (3,("D",""),eNode,Node (2,("B",""),cNode,aNode)))
        let actual = right_app func1 (Node (3,("D",""),eNode,Node (2,("B",""),aNode,cNode)))
                                                    
        actual
        |> should equal expected

    (* decrease_level tests *)

    [<Fact>]
    let ``decrease_level_less_test``() =

        decrease_level 2 (Node (3,("D",""),Node (2,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))
        |> should equal (Node (2,("D",""),Node (2,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))

    [<Fact>]
    let ``decrease_level_equal_test``() =

        decrease_level 3 (Node (3,("D",""),Node (2,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))
        |> should equal (Node (3,("D",""),Node (2,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))

    [<Fact>]
    let ``decrease_level_greater_test``() =

        decrease_level 4 (Node (3,("D",""),Node (2,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))
        |> should equal (Node (3,("D",""),Node (2,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))

    (* skew tests *)

    [<Fact>]
    let ``skew_test``() = 

        //          D[n]                     B[n]                                  
        //         /    \                   /    \                                 
        //       B[n]  E[..]     -->     A[..]  D[n]                               
        //      /   \                           /   \                              
        //   A[..]  C[..]                    C[..]  E[..]

        let input = (Node (3,("D",""),Node (3,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (2,("E",""),Leaf,Leaf)))
        let expected = (Node (3,("B",""),Node (1,("A",""),Leaf,Leaf),Node (3,("D",""),Node (1,("C",""),Leaf,Leaf),Node (2,("E",""),Leaf,Leaf))))
        let actual = skew input

        actual
        |> should equal expected

    (* split tests *)

    [<Fact>]
    let ``split_test``() = 

        //        B[n]                      D[n+1]    
        //       /    \                     /    \    
        //    A[..]  D[n]      -->        B[n]  E[n]  
        //           /  \                /   \        
        //       C[..]  E[n]          A[..]  C[..] 

        let input = (Node (3,("B",""),Node (1,("A",""),Leaf,Leaf),Node (3,("D",""),Node (1,("C",""),Leaf,Leaf),Node (3,("E",""),Leaf,Leaf))))
        let expected = (Node (4,("D",""),Node (3,("B",""),Node (1,("A",""),Leaf,Leaf),Node (1,("C",""),Leaf,Leaf)),Node (3,("E",""),Leaf,Leaf)))
        let actual = split input

        actual
        |> should equal expected

    (* dltree_insert tests *)

    [<Fact>]
    let ``dltree_insert_test``() = 

        // First insert inserts on th right
        //
        //        (1,A)[1]    
        //              \     
        //           (2,B)[1] 

        let expected = Node (1,(1,"A"),Leaf,Node (1,(2,"B"),Leaf,Leaf))
        let actual = 
            Leaf 
            |> dltree_insert (1,"A") 
            |> dltree_insert (2,"B")

        actual
        |> should equal expected

    [<Fact>]
    let ``dltree_insert_split_test``() = 

        // Second insert inserts on the left but because has the same level of the parent
        // causes a split to rebalance
        //
        //        (1,A)[1]                (2,B)[2]    
        //              \                 /     \    
        //           (2,B)[1]    -->  (1,A)[1]  (3,C)[1]   
        //

        let expected = Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (1,(3,"C"),Leaf,Leaf))
        let actual = 
            Leaf 
            |> dltree_insert (1,"A") 
            |> dltree_insert (2,"B")
            |> dltree_insert (3,"C")

        actual
        |> should equal expected

    [<Fact>]
    let ``dltree_insert_3_test``() = 

        // Second insert inserts on the left but because has the same level of the parent
        // causes a split to rebalance
        //
        //       (2,B)[2]                         (2,B)[2]    
        //       /     \                          /     \    
        //   (1,A)[1]  (3,C)[1]               (1,A)[1]  (3,C)[1] 
        //                                                 \
        //                                                 (4,D)[1]
        //
        //

        let expected = Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (1,(3,"C"),Leaf,Node (1,(4,"D"),Leaf,Leaf)))
        let actual = 
            Leaf 
            |> dltree_insert (1,"A") 
            |> dltree_insert (2,"B")
            |> dltree_insert (3,"C")
            |> dltree_insert (4,"D")

        actual
        |> should equal expected

    [<Fact>]
    let ``dltree_insert_4_test``() = 

        // Second insert inserts on the left but because has the same level of the parent
        // causes a split to rebalance
        //
        //             (2,B)[2]                          (2,B)[2]    
        //             /     \                           /     \    
        //         (1,A)[1]  (3,C)[1]         -->     (1,A)[1]  (4,D)[2] 
        //                      \                              /       \
        //                      (4,D)[1]                    (3,C)[1]   (5,E)[1]
        //
        //

        let expected = Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (2,(4,"D"),Node (1,(3,"C"),Leaf,Leaf),Node (1,(5,"E"),Leaf,Leaf)))
        let actual = 
            Leaf 
            |> dltree_insert (1,"A") 
            |> dltree_insert (2,"B")
            |> dltree_insert (3,"C")
            |> dltree_insert (4,"D")
            |> dltree_insert (5,"E")

        actual
        |> should equal expected

    [<Fact>]
    let ``dltree_insert_6_test``() = 

        // Second insert inserts on the left but because has the same level of the parent
        // causes a split to rebalance
        //
        //        (2,B)[2]                                              (4,D)[3]                     
        //        /     \                                     __________/     \__________                 
        //     (1,A)[1]  (4,D)[2]            -->             /                           \                 
        //              /       \                         (2,B)[2]                      (6,F)[2]            
        //           (3,C)[1]   (5,E)[1]                  /       \                     /       \                
        //                                            (1,A)[1]   (3,C)[1]         (5,E)[1]   (7,G)[1]         
        //                                                                     
        //             

        let expected = Node (3,(4,"D"),
                        Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (1,(3,"C"),Leaf,Leaf)),
                        Node (2,(6,"F"),Node (1,(5,"E"),Leaf,Leaf),Node (1,(7,"G"),Leaf,Leaf)))

        let actual = 
            Leaf 
            |> dltree_insert (1,"A") 
            |> dltree_insert (2,"B")
            |> dltree_insert (3,"C")
            |> dltree_insert (4,"D")
            |> dltree_insert (5,"E")
            |> dltree_insert (6,"F")
            |> dltree_insert (7,"G") 

        actual
        |> should equal expected

    (* dltree_delete tests *)

    [<Fact>]
    let ``dltree_delete_test``() = 

        let input = Node (3,(4,"D"),
                        Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (1,(3,"C"),Leaf,Leaf)),
                        Node (2,(6,"F"),Node (1,(5,"E"),Leaf,Leaf),Node (1,(7,"G"),Leaf,Leaf)))

        let expected = Node (3,(4,"D"),
                        Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (1,(3,"C"),Leaf,Leaf)),
                        Node (1,(5,"E"),Leaf,Leaf))

        let actual = 
            input
            |> dltree_delete 6
            |> dltree_delete 7

        actual
        |> should equal expected

    (* dltree_elem tests *)

    [<Fact>]
    let ``dltree_elem_test``() = 

        let input = Node (3,(4,"D"),
                        Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (1,(3,"C"),Leaf,Leaf)),
                        Node (2,(6,"F"),Node (1,(5,"E"),Leaf,Leaf),Node (1,(7,"G"),Leaf,Leaf)))

        input 
        |> dltree_elem 5
        |> should equal (5, "E")

    //TODO: aggiungere un fail test

    (* dltree_lookup tests *)

    [<Fact>]
    let ``dltree_lookup_test``() = 

        let input = Node (3,(4,"D"),
                        Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (1,(3,"C"),Leaf,Leaf)),
                        Node (2,(6,"F"),Node (1,(5,"E"),Leaf,Leaf),Node (1,(7,"G"),Leaf,Leaf)))

        input 
        |> dltree_lookup 5
        |> should equal "E"

    //TODO: aggiungere un fail test

    (* dltree_mem tests *)

    [<Fact>]
    let ``dltree_mem_true_test``() = 

        let input = Node (3,(4,"D"),
                        Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (1,(3,"C"),Leaf,Leaf)),
                        Node (2,(6,"F"),Node (1,(5,"E"),Leaf,Leaf),Node (1,(7,"G"),Leaf,Leaf)))

        input 
        |> dltree_mem 5
        |> should equal true

    [<Fact>]
    let ``dltree_mem_false_test``() = 

        let input = Node (3,(4,"D"),
                        Node (2,(2,"B"),Node (1,(1,"A"),Leaf,Leaf),Node (1,(3,"C"),Leaf,Leaf)),
                        Node (2,(6,"F"),Node (1,(5,"E"),Leaf,Leaf),Node (1,(7,"G"),Leaf,Leaf)))

        input 
        |> dltree_mem 12
        |> should equal false