
module DATALOG-SYNTAX

	syntax Term ::= String
				|	Id
				|   Int
	
	syntax Terms ::= List{Term,","}
	
	syntax PredicateSymbol ::= Id
	
	syntax Literal ::= PredicateSymbol "(" Terms ")"
					
	syntax Literals ::= List{Literal,","}
					
	syntax Clause ::= Literal ":-" Literals
					
	syntax Clauses ::= List{Clause,","}
					
	syntax Stmt ::= Clause "."
				> 	Clause "." Stmt
	
	syntax Query ::= Literal "?"
	
	syntax Queries ::= Literals "s?"
	
	syntax Program ::= Stmt Query
	
endmodule

module DATALOG
  imports DATALOG-SYNTAX
  
  syntax MaybeLiteral ::= Some(Literal) | "None"
  
  syntax K ::= unifys(Terms, Terms) | "does not unify" | unify(Term, Term) 
			| FindMatchingClauses(Clauses, Literal) | print(K) | "active" MaybeLiteral
			|NormalizeL(Literal)	| Normalize( Int, Map, Terms ) | NormalizeFL(Literals) 
			| Sub(Terms, Map) | SubT(Term, Map) | SubLs(Literals, Map) | SubL(Literal, Map) 
			| "done" | "applySub" | Mgu(Map) //if Map contains(X |-> Y) then X <String Y
			| NormalizeMaybe(MaybeLiteral) | SubMaybe(MaybeLiteral, Map) | First(Literals) | printS(String)
			| canUnify(Terms, Terms) | "True" | "False"
	
  syntax Val ::= String
			 |	 Int
  
  
	configuration <C>
					<threads>
						<thread multiplicity="*">
							<k> $PGM:Program </k>
							<Root> .K </Root>
							<Clause> .K </Clause>
							<Used> .Set </Used>
						</thread>
                    </threads>
                    <Database> .Clauses </Database>	
					<Table> .Set </Table>		
					<printer> .K </printer>
					<originalQuery> .K </originalQuery>
					<globalout stream="stdout"> .List </globalout>
					
                </C>
				
	rule [Assertion]:
		<k> ( C:Clause . S:Stmt Q:Query => S Q)</k>
		<Database> D:Clauses => C, D </Database>
		
	rule [Assertion-Last-Clause]:
		<k> ( C:Clause . Q:Query => Q ) </k>
		<Database> D:Clauses => C, D </Database>		
	
	rule [Query-Copy-Data]:
		<k> (S:PredicateSymbol ( T:Terms ) ? => FindMatchingClauses(D, S ( Normalize(0, .Map, T) ) )) ...</k> 		
		<Database>D:Clauses</Database>
		<Table> . => SetItem( S ( Normalize(0, .Map, T) ), . ) </Table>
		<originalQuery> . => S:PredicateSymbol ( T:Terms ) </originalQuery>
		
	
	rule [New-Root-In-List]:
		<k> FindMatchingClauses(S:PredicateSymbol (T2:Terms) :- Ls:Literals, D:Clauses, S ( T:Terms ) ) 
			=> FindMatchingClauses(D, S ( T ) ) </k>  
		(. => <thread>... <k> unifys(T2, T) ~> applySub ~> active First(Ls) </k> 
						  <Root> S ( T ) ?</Root>
						  <Clause> S ( T2 ) :- Ls </Clause>
						  <Used> .Set </Used>
						  ...</thread>) 
		
	rule [New-Root-Not-In-List]:
		<k> FindMatchingClauses(S1:PredicateSymbol (T2:Terms) :- Ls:Literals, D:Clauses, S:PredicateSymbol ( T:Terms ) ) 
			=> FindMatchingClauses(D:Clauses, S:PredicateSymbol ( T:Terms ) ) </k> 
		when notBool(Id2String(S1) ==String Id2String(S))
		
	rule [New-Root-Empty]:
		<thread>
		<k> FindMatchingClauses(.Clauses, L:Literal) ...</k>
		...</thread> => .	
	
	rule [Active-Node-In-Table]:
		<k> active Some(S1:PredicateSymbol ( T1:Terms )) </k>
		<Root> R ?</Root>
		<Clause> H:Literal :- S:PredicateSymbol ( Ts:Terms ), Ls:Literals </Clause>
		<Used> U:Set => U SetItem(S1 ( T1 ), S2 ( T2 ) )</Used>
		<Table>... SetItem( S1 ( T1 ), S2:PredicateSymbol ( T2:Terms ) ) ...</Table>
		(. => <thread>... <k>unifys(Ts, T2) ~> applySub ~> active First(Ls) </k>
				  <Root> R ?</Root>
				  <Clause> H :- Ls </Clause>
			...</thread>)
		when notBool (S1 ( T1 ), S2 ( T2 )) in U
		
	rule [First-Empty]:
		First(.Literals) => None [anywhere]
		
	rule [First-Not-Empty]:
		First(L:Literal, Ls:Literals) => Some(L) [anywhere]

	rule [Active-Node-Not-In-Table]:
		<k> active Some(S:PredicateSymbol ( Ts:Terms )) </k>
		<Table> T:Set => T SetItem( S ( Ts ), . ) </Table>
		<Database>D:Clauses</Database>
		(. => <thread>... <k> FindMatchingClauses(D, S ( Ts ))</k>
			...</thread>)
		when notBool (S ( Ts ), .)  in T
		
	rule [Add-Answer-to-Table]:
		(<thread>
		<k> active None </k> 
		<Root> S:PredicateSymbol ( Ts:Terms ) ?</Root>
		<Clause> S1:PredicateSymbol ( T1s:Terms ) :- .Literals </Clause>
		...</thread> => .)
		<Database>D:Clauses => S1 ( T1s ) :- .Literals, D </Database>
		<Table>... . => SetItem(S ( Normalize(0, .Map, Ts) ), S1 ( T1s )) ...</Table>
		<printer> X => X ~> print(S1 ( T1s )) </printer>
		
	
	syntax K ::= resolveAmbiguityLiterals(Literals) | resolveAmbiguityTerms(Terms)
	rule resolveAmbiguityLiterals(X) => X [anywhere]
	rule resolveAmbiguityTerms(X) => X [anywhere]
	
	rule [Apply-Substitution]:
		<k> Mgu(M:Map) ~> applySub ~> active ML:MaybeLiteral
			=> active NormalizeMaybe(SubMaybe(ML, M)) </k>
		<Clause> S:PredicateSymbol ( T:Terms ) :- Ls:Literals => S ( Sub(T, M)) :- SubLs(Ls, M)  </Clause>
	
	rule NormalizeMaybe(Some(L)) => Some(NormalizeL(L)) [anywhere]
	rule NormalizeMaybe(None) => None [anywhere]
	
	rule [Normalize-Literal]:
		NormalizeL( S:PredicateSymbol ( T:Terms )) => S ( Normalize( 0, .Map, T) ) [anywhere]
	
	rule SubMaybe(Some(L), M:Map) => Some(SubL(L, M)) [anywhere]
	rule SubMaybe(None, M) => None [anywhere]
	
	rule [Sub-Literals]:
		SubLs(L:Literal, Ls:Literals, M:Map) => resolveAmbiguityLiterals(SubL(L, M), SubLs(Ls, M)) [anywhere]
		
	rule [Sub-Literals-Empty]:
		SubLs(.Literals, M:Map) => .Literals [anywhere]
		
	rule [Sub-Literal]:
		SubL(S:PredicateSymbol ( T:Terms ), M:Map) => S ( Sub(T, M) ) [anywhere]
	
	rule [Sub]:
		Sub(T:Term, Ts:Terms, M:Map) => resolveAmbiguityTerms(SubT(T, M), Sub(Ts, M)) [anywhere]
		
	rule [Sub-Empty]:
		Sub(.Terms, M:Map) => .Terms [anywhere]
		
	rule [Sub-Id-In-Map]:
		SubT(I:Id, M:Map(I |-> X)) => X  [anywhere]

		
	rule [Sub-Id-not-In-Map]:
		SubT(I:Id, M:Map) => I 
		when notBool(I in keys(M)) [anywhere]
		
	rule [Sub-Value]:
		SubT(V:Val, M:Map) => V [anywhere]
		
	rule [Normalize-Terms-Val]:
		Normalize( C:Int, M:Map, V:Val, Ts:Terms) => resolveAmbiguityTerms(V, Normalize(C, M, Ts)) [anywhere]
		
	rule [Normalize-Terms-Id]:
		Normalize(C:Int, M:Map, I:Id, Ts:Terms) => String2Id("X" +String Int2String(C)), Normalize( C +Int 1, M(I |-> String2Id("X" +String Int2String(C))), Ts) 
		when notBool(I in keys(M))[anywhere]
		
	rule [Normalize-Terms-Id]:
		Normalize(C:Int, M:Map(I |-> X:Id), I:Id, Ts:Terms) => X, Normalize( C +Int 1, M, Ts) 

		
	rule [Normalize-Terms-Empty]:
		Normalize(C:Int, M:Map, .Terms) => .Terms [anywhere]
	
	
	rule [unify-begin]:
		<k> unifys(T1s:Terms, T2s:Terms) => Mgu(.Map) ~> unifys(T1s, T2s) ...</k> 
	
	rule [unify-pair]:
		<k> Mgu(M:Map) ~> unifys(T1:Term, T1s:Terms, T2:Term, T2s:Terms) => Mgu(M) ~> unify(T1, T2) ~> unifys(T1s, T2s) ...</k> 
		
	rule [unify-empty]:
		<k> Mgu(M:Map) ~> unifys(.Terms, .Terms) => Mgu(M) ...</k>
	
	rule [unify-equal]:
		<k> Mgu(M:Map) ~> unify(V1:Val, V1) => Mgu(M) ...</k>
		
	rule [unify-to-val-new]:
		<k> Mgu(M:Map) ~> unify(I:Id, V:Val) => Mgu(M(I |-> V))  ...</k>
		when notBool(I in keys(M))
		
	rule [unify-to-val-known]:
		<k> Mgu(M:Map(I |-> V)) ~> unify(I:Id, V:Val) => Mgu(M(I |-> V)) ...</k>
		
	rule [unify-to-val-continue]:
		<k> Mgu(M:Map(I |->J:Id)) ~> unify((I:Id => J), V:Val) ...</k>
		
	rule [unify-to-val-wrong-order]:
		<k> Mgu(M:Map) ~> unify(V:Val, I:Id) => Mgu(M) ~> unify(I, V) ...</k>
		
	rule [Unify-to-Id-Same]:
		<k> Mgu(M:Map) ~> unify(I1:Id, I1) => Mgu(M) ...</k>
		
	rule [Unify-to-Id-Out-of-Order]:
		<k> Mgu(M:Map) ~> (unify(I2:Id, I1:Id) => unify(I1, I2)) ...</k>
		when Id2String(I1) <String Id2String(I2)

	rule [Unify-to-Id-New]:
		<k> Mgu(M:Map) ~> unify(I1:Id, I2:Id) => Mgu(M(I1 |-> I2)) ...</k>
		when (Id2String(I1) <String Id2String(I2)) andBool (notBool(I1 in keys(M)))
	
	rule [Unify-to-Id-In-Order]:
		<k> Mgu(M:Map(I1:Id |-> I2:Id)) ~> (unify(I1, I3:Id) => unify(I2, I3)) ...</k>
		when (Id2String(I1) <String Id2String(I2)) 
		andBool (Id2String(I2) <String Id2String(I3)) 
		
	rule [Unify-to-Id-In-Order]:
		<k> Mgu(M:Map(I1:Id |-> I3:Id)) ~> unify(I1, I2:Id) => Mgu(M(I1 |-> I2)) ~> unify(I2, I3) ...</k>
		when (Id2String(I1) <String Id2String(I2)) 
		andBool (Id2String(I2) <String Id2String(I3)) 
		
	rule [print]:
		<printer> True ~> print( S:PredicateSymbol ( Ts:Terms ) )=> print(S) ~> printS("(") ~> print(Ts) ~> printS(")\n") ...</printer>

	rule [print]:
		<printer> False ~> print( S:PredicateSymbol ( Ts:Terms ) )=> . ...</printer>
	
	rule	<printer> canUnify(S:String, Ts:Terms, S, T2s:Terms) => canUnify(Ts, T2s) ...</printer>

	rule	<printer> canUnify((S:String, Ts:Terms), (S2:String, T2s:Terms)) => False ...</printer>
		when notBool(S ==String S2)

	rule	<printer> canUnify(V:Val, Ts:Terms, I:Id, T2s:Terms) => canUnify(Ts, T2s) ...</printer>

	rule	<printer> canUnify(I:Id, Ts:Terms, V:Val, T2s:Terms) => canUnify(Ts, T2s) ...</printer>

	rule	<printer> canUnify(I:Int, Ts:Terms, I, T2s:Terms) => canUnify(Ts, T2s) ...</printer>
	rule	<printer> canUnify(.Terms, .Terms) => True ...</printer>

	rule	<printer> canUnify(I:Int, Ts:Terms, I2:Int, T2s:Terms) => False ...</printer>
		when notBool(I ==Int I2)

	rule	<printer> canUnify(I:Int, Ts:Terms, S:String, T2s:Terms) => False ...</printer>
	rule	<printer> canUnify(S:String, Ts:Terms, I:Int, T2s:Terms) => False ...</printer>
	
	rule [print]:
		<printer> print( S:PredicateSymbol ( Ts:Terms ) )=> canUnify(Ts, T2s) ~> print( S ( Ts ) ) ...</printer>
		<originalQuery> S ( T2s:Terms ) </originalQuery>
		when (lengthTList(Ts) ==Int lengthTList(T2s))
		
	rule [print]:
		<printer> print( S:PredicateSymbol ( Ts:Terms ) )=> . ...</printer>
		<originalQuery> S1:PredicateSymbol ( T2s:Terms ) </originalQuery>
		when notBool((Id2String(S) ==String Id2String(S1)) andBool (lengthTList(Ts) ==Int lengthTList(T2s)))
	
	rule 
		<printer> print( I:Id ) => . ...</printer>
		<globalout>... (. => ListItem(Id2String(I))) </globalout>
		
	rule 
		<printer> print( .Terms ) => . ...</printer>
		
	rule
		<printer> print( T:Term, .Terms) => print(T) ...</printer>
		
	rule
		<printer> print( T:Term, Ts:Terms) => print(T) ~> printS(",") ~> print(Ts) ...</printer>
		when notBool(lengthTList(Ts) ==Int 0)
		
	rule
		<printer> printS( S:String ) => . ...</printer>
		<globalout>... (. => ListItem(S)) </globalout>

	rule
		<printer> print( S:String ) => . ...</printer>
		<globalout>... (. => ListItem("\"" +String S +String "\"")) </globalout>	

	rule
		<printer> print( I:Int ) => . ...</printer>
		<globalout>... (. => ListItem(Int2String(I))) </globalout>
	
	
	syntax Int ::= "lengthTList" Terms [function]

   rule lengthTList ( T:Term, Ts:Terms ) => 1 +Int lengthTList Ts [structural, anywhere]
   rule lengthTList .Terms => 0 [structural, anywhere]
	
		
  
endmodule
