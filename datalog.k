
module DATALOG-SYNTAX

	syntax Term ::= String
				|	Id
				|   Int
	
	syntax Terms ::= List{Term,","}
	
	syntax PredicateSymbol ::= Id
	
	syntax Literal ::= PredicateSymbol "(" Terms ")"
					
	syntax Literals ::= List{Literal,","}
					
	syntax Clause ::= Literal ":-" Literals

	syntax Fact ::= Literal "."
					
	syntax Clauses ::= List{Clause,","}
					
	syntax Stmt ::= Clause "."
				|	Fact				
				| 	Clause "." Stmt
				|	Fact Stmt
				
	
	syntax Query ::= Literal "?"
	
	syntax Queries ::= Literals "s?"
	
	syntax Program ::= Stmt Query
	
endmodule

module DATALOG
  imports DATALOG-SYNTAX
  
  syntax K ::= unifys(Terms, Terms) | "does not unify" | unify(Term, Term) 
			| FindMatchingClauses(Set, Literal) | print(K) 
			| Sub(Terms, Map) | SubT(Term, Map) | SubLs(Literals, Map) | SubL(Literal, Map) 
			| "done" | "applySub" | Mgu(Map) //if Map contains(X |-> Y) then X <String Y
			| First(Literals) | printS(String)
			| canUnify(Terms, Terms) | "True" | "False" | "NewGoal" | "Init" 
			| Freshen(Int, Terms) | FreshenLs(Int, Literals) | FreshenL(Int, Literal)
			| Contains(Set, Literal) | Compare(Terms, Terms) | CompareT(Term, Term)

  syntax Broadcast ::= Int "," Fact

  syntax Set ::= NormalizeS(Set)

  syntax K ::= NormalizeL(Literal) [function]
  syntax K ::= Normalize( Int, Map, Terms ) [function] 

  syntax Val ::= String
			 |	 Int
  
  
	configuration <C>
					<threads>
						<thread multiplicity="*">
							<k> $PGM:Program </k>
							<Used> .Set </Used>
							<Usable> .Set </Usable>
							<Id> 0 </Id>
						</thread>
                    </threads>
                    <Database> .Set </Database>	
					<Rulebase> .Set </Rulebase>
					<Table> .Set </Table>
					<Broadcast> .Set </Broadcast>
					<Dead> .Set </Dead>
					<Active> 0 </Active>
					<freshen> 0 </freshen>	
					<IdCounter> 0 </IdCounter>
					<printer> .K </printer>
					<originalQuery> .K </originalQuery>
					<globalout stream="stdout"> .List </globalout>
                </C>
				
	rule [Assertion]:
		<k> ( C:Clause . S:Stmt Q:Query => S Q)</k>
		<Rulebase> R:Set => R SetItem(C) </Rulebase>

	rule [Assertion]:
		<k> ( F:Fact S:Stmt Q:Query => S Q)</k>
		<Database> D:Set => D SetItem(F) </Database>	
		
	rule [Assertion-Last-Clause]:
		<k> ( C:Clause . Q:Query => Q ) </k>
		<Rulebase> R:Set => R SetItem(C) </Rulebase>
	
	rule [Assertion-Last-Clause]:
		<k> ( F:Fact Q:Query => Q ) </k>
		<Database> D:Set => D SetItem(F) </Database>		
	
	rule [Query-Copy-Data]:
		<k> (S:PredicateSymbol ( T:Terms ) ? => FindMatchingClauses(D, S ( Normalize(0, .Map, T) ) )) ...</k> 		
		<Rulebase>D:Set</Rulebase>
		<Table> . => SetItem( S ( Normalize(0, .Map, T) )) </Table>
		<originalQuery> . => S:PredicateSymbol ( T:Terms ) </originalQuery>
		
	
	rule [New-Root-In-List]:
		<k> FindMatchingClauses(SetItem(S:PredicateSymbol (T2:Terms) :- Ls:Literals) R:Set, S ( T:Terms ) ) 
			=> FindMatchingClauses(R, S ( T ) ) </k>  
		(. => <thread>... <k> unifys(Freshen(N, T2), T) ~> Init ~> applySub ~> S ( Freshen(N, T2) ) :- FreshenLs(N, Ls) </k> 
						  <Used> .Set </Used>
						  <Usable> D </Usable>
						  <Id> I </Id>
						  ...</thread>) 
		<freshen> N:Int => N +Int 1 </freshen>
		<Database> D:Set </Database>
		<IdCounter> I:Int => I +Int 1 </IdCounter>
		
	rule [New-Root-Not-In-List]:
		<k> FindMatchingClauses(SetItem(S1:PredicateSymbol (T2:Terms) :- Ls:Literals) D:Set, S:PredicateSymbol ( T:Terms ) ) 
			=> FindMatchingClauses(D, S:PredicateSymbol ( T:Terms ) ) </k> 
		when notBool(Id2String(S1) ==String Id2String(S))
		
	rule [New-Root-Empty]:
		<thread>
		<k> FindMatchingClauses(.Set, L:Literal) ...</k>
		...</thread> => .
	
	rule [Active-Node-Check-Table]:
		<k> Init ~> H:Literal :- S:PredicateSymbol ( Ts:Terms ), Ls:Literals 
				 => Contains(NormalizeS(T), NormalizeL(S ( Ts ))) ~> H :- S ( Ts ), Ls ...</k>
		<Table> T:Set </Table>

	rule NormalizeS(SetItem(I:Literal) T:Set) => SetItem(NormalizeL(I)) NormalizeS(T) [anywhere]
	rule NormalizeS(.Set) => .Set [anywhere]	

	rule <k> Contains(SetItem(L) T:Set, L:Literal)
		 => . ...</k>

	rule <k> Contains(T:Set, L:Literal)
		 => NewGoal ...</k>
		 when notBool(L in T)
		 	
	rule [Active-Node-Not-In-Table]:
		<k> NewGoal ~> H:Literal :- S:PredicateSymbol ( Ts:Terms ), Ls:Literals 
				 =>  H:Literal :- S ( Ts ), Ls </k>
		<Table> T:Set => T SetItem( S ( Ts )) </Table>
		<Rulebase>R:Set</Rulebase>
		<Database> D:Set </Database>
		(. => <thread>... <k> FindMatchingClauses(R, S ( Ts ))</k>
			...</thread>)

	rule [Active-Node-In-Table]:
		<k> H:Literal :- S1:PredicateSymbol ( T1:Terms ), Ls:Literals </k>
		<Usable> SetItem(S1 ( T2:Terms ) .) S:Set => S </Usable>
		<Used> U:Set => U SetItem(S1 ( T2 ))</Used>
		<Database> D </Database>
		<IdCounter> I:Int => I +Int 1 </IdCounter>
		(. => <thread>... <k>unifys(T1, T2) ~> Init ~> applySub ~> H :- Ls </k>
						  <Usable> D </Usable>
						  <Id> I </Id>
			...</thread>)
		when notBool (S1 ( T2 )) in U

	rule [Broadcast]:
		<threads>...		
			<thread>...
				<Usable>... . => SetItem(F) ...</Usable>
				<Id> I </Id>
			...</thread>
		...</threads>
		<Broadcast> SetItem(I:Int, F:Fact) B:Set => SetItem(I +Int 1, F) B </Broadcast>

	rule [Dead-Id]:
		<Broadcast> SetItem(I, F:Fact) B:Set => SetItem(I +Int 1, F) B </Broadcast>
		<Dead>... SetItem(I:Int) ...</Dead>

	rule [End-Broadcast]:
		<Broadcast> SetItem(I, F:Fact) B:Set => B </Broadcast>
		<IdCounter> I2:Int </IdCounter>
		when I ==Int I2
		

	rule [First-Empty]:
		First(.Literals) => . [anywhere]
		
	rule [First-Not-Empty]:
		First(L:Literal, Ls:Literals) => L ?[anywhere]
		
	rule [Add-Answer-to-Database]:
		(<thread>
		<k> Init ~> S1:PredicateSymbol ( T1s:Terms ) :- .Literals </k>
		<Id> I:Int </Id>
		...</thread> => .)
		<Database>D:Set => SetItem(S1 ( T1s ) .) D </Database>
		<Broadcast>... . => SetItem(0, S1 ( T1s ) .) ...</Broadcast>
		<Dead>... . => SetItem(I) ...</Dead>
		<printer> X => X ~> print(S1 ( T1s )) </printer>
		
	
	syntax K ::= resolveAmbiguityLiterals(Literals) | resolveAmbiguityTerms(Terms) | resolveAmbiguityLiteral(Literal)
	rule resolveAmbiguityLiterals(X) => X [anywhere]
	rule resolveAmbiguityTerms(X) => X [anywhere]
	rule resolveAmbiguityLiteral(X) => X [anywhere]

	rule [Apply-Substitution]:
		<k> Mgu(M:Map) ~> Init ~> applySub ~> S:PredicateSymbol ( T:Terms ) :- Ls:Literals => Init ~> S ( Sub(T, M)) :- SubLs(Ls, M)</k>
	
	rule NormalizeL( S:PredicateSymbol ( T:Terms )) => S ( Normalize( 0, .Map, T) ) [anywhere]
	rule NormalizeL( . ) => . [anywhere]

	rule FreshenLs(N:Int, L:Literal, Ls:Literals) => resolveAmbiguityLiterals(FreshenL(N, L), FreshenLs(N, Ls))[anywhere]
	rule FreshenLs(N, .Literals ) => .Literals [anywhere]

	rule FreshenL(N, S:PredicateSymbol ( T:Terms )) => resolveAmbiguityLiteral(S ( Freshen(N, T) )) [anywhere]
	rule FreshenL(N, .) => . [anywhere]
	
	rule [Sub-Literals]:
		SubLs(L:Literal, Ls:Literals, M:Map) => resolveAmbiguityLiterals(SubL(L, M), SubLs(Ls, M)) [anywhere]
		
	rule [Sub-Literals-Empty]:
		SubLs(.Literals, M:Map) => .Literals [anywhere]
		
	rule SubL(S:PredicateSymbol ( T:Terms ), M:Map) => S ( Sub(T, M) ) [anywhere]
	rule SubL(. , M:Map) => . [anywhere]
	
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

	rule Freshen(N:Int, V:Val, Ts:Terms) => resolveAmbiguityTerms(V, Freshen(N, Ts)) [anywhere]
	rule Freshen(N:Int, I:Id, Ts:Terms) => String2Id(Id2String(I) +String "_" +String Int2String(N)), Freshen( N, Ts) [anywhere]
	rule Freshen(N:Int, .Terms ) => .Terms [anywhere]
		
	rule [Normalize-Terms-Val]:
		Normalize( C:Int, M:Map, V:Val, Ts:Terms) => resolveAmbiguityTerms(V, Normalize(C, M, Ts)) [anywhere]
		
	rule [Normalize-Terms-Id]:
		Normalize(C:Int, M:Map, I:Id, Ts:Terms) => String2Id("X" +String Int2String(C)), Normalize( C +Int 1, M(I |-> String2Id("X" +String Int2String(C))), Ts) 
		when notBool(I in keys(M))[anywhere]
		
	rule [Normalize-Terms-Id]:
		Normalize(C:Int, M:Map(I |-> X:Id), I:Id, Ts:Terms) => X, Normalize( C +Int 1, M, Ts) [anywhere]

		
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
