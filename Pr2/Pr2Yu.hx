// [NYU Courant Institute] Compiler Construction/Fall 2015 -*-hacs-*-
//
// Grammar and some utilities  for Milestone 2 (remember to rename).
//
// Based on "Pr1Rose.hx"[1] extended with rules from "Pr2Rose-SDD"[2] solution
// and some helpers developed during lecture 8.
//
// [1]\url{http://cs.nyu.edu/courses/fall15/CSCI-GA.2130-001/project1/Pr1Rose.hx}
// [2]\url{http://cs.nyu.edu/courses/fall15/CSCI-GA.2130-001/project2/SubScript-SDD.pdf}
//
// This file is Copyright © 2015 Kristoffer Rose ⟨krisrose@crsx.org⟩
// and licensed under the CC-BY-4.0 license ().

module edu.nyu.csci.cc.fall15.Pr2Yu {

  ////////////////////////////////////////////////////////////////////////
  // GRAMMAR FROM MILESTONE 1.
  //
  // [1] references are to the Project Milestone 1 assignment.
  
  // LEXICAL CONVENTIONS ([1]1.1).

  // Ignore:
  space [ \t\n\r] | "//" .*			// white space
    | "/*" ( [^*] | "*" [^/] )* "*/"  ;		// non-nested C comments

  // We have identifiers, integers, and strings.
  token IDENTIFIER  | ⟨LetterEtc⟩ (⟨LetterEtc⟩ | ⟨Digit⟩)* ;
  token INTEGER     | ⟨Digit⟩+ ;
  token STRING      | "\'" ( [^\'\\\n] | \\ ⟨Escape⟩ )* "\'"
    | "\"" ( [^\"\\\n] | \\ ⟨Escape⟩ )* "\""
    ;

  // Lexical helpers.
  token fragment Letter     | [A-Za-z] ;
  token fragment LetterEtc  | ⟨Letter⟩ | [$_] ;
  token fragment Digit      | [0-9] ;
  token fragment Escape  | [\n\\nt''""] | "x" ⟨Hex⟩ ⟨Hex⟩ ;
  token fragment Hex     | [0-9A-Fa-f] ;

  // EXPRESSIONS ([1]1.2).
  //
  // Each operator is assigned a \HAX precendence following Figure 1.

  sort Expression

    |  ⟦ ⟨IDENTIFIER⟩ ⟧@13
    |  ⟦ ⟨STRING⟩ ⟧@13
    |  ⟦ ⟨INTEGER⟩ ⟧@13
    |  sugar ⟦ ( ⟨Expression#e⟩ ) ⟧@13 → #e

    |  ⟦ ⟨Expression@12⟩ . ⟨IDENTIFIER⟩ ⟧@12
    |  ⟦ ⟨Expression@12⟩ ( ⟨ExpressionList⟩ ) ⟧@12

    |  ⟦ ! ⟨Expression@11⟩ ⟧@11
    |  ⟦ ~ ⟨Expression@11⟩ ⟧@11
    |  ⟦ - ⟨Expression@11⟩ ⟧@11
    |  ⟦ + ⟨Expression@11⟩ ⟧@11

    |  ⟦ ⟨Expression@10⟩ * ⟨Expression@11⟩ ⟧@10
    |  ⟦ ⟨Expression@10⟩ / ⟨Expression@11⟩ ⟧@10
    |  ⟦ ⟨Expression@10⟩ % ⟨Expression@11⟩ ⟧@10

    |  ⟦ ⟨Expression@9⟩ + ⟨Expression@10⟩ ⟧@9
    |  ⟦ ⟨Expression@9⟩ - ⟨Expression@10⟩ ⟧@9

    |  ⟦ ⟨Expression@9⟩ < ⟨Expression@9⟩ ⟧@8
    |  ⟦ ⟨Expression@9⟩ > ⟨Expression@9⟩ ⟧@8
    |  ⟦ ⟨Expression@9⟩ <= ⟨Expression@9⟩ ⟧@8
    |  ⟦ ⟨Expression@9⟩ >= ⟨Expression@9⟩ ⟧@8

    |  ⟦ ⟨Expression@8⟩ == ⟨Expression@8⟩ ⟧@7
    |  ⟦ ⟨Expression@8⟩ != ⟨Expression@8⟩ ⟧@7

    |  ⟦ ⟨Expression@6⟩ & ⟨Expression@7⟩ ⟧@6
    |  ⟦ ⟨Expression@5⟩ ^ ⟨Expression@6⟩ ⟧@5
    |  ⟦ ⟨Expression@4⟩ | ⟨Expression@5⟩ ⟧@4

    |  ⟦ ⟨Expression@3⟩ && ⟨Expression@4⟩ ⟧@3
    |  ⟦ ⟨Expression@2⟩ || ⟨Expression@3⟩ ⟧@2

    |  ⟦ ⟨Expression@2⟩ ? ⟨Expression⟩ : ⟨Expression@1⟩ ⟧@1

    |  ⟦ ⟨Expression@1⟩ = ⟨Expression⟩ ⟧
    |  ⟦ ⟨Expression@1⟩ += ⟨Expression⟩ ⟧
    |  ⟦ ⟨Expression@1⟩ = { ⟨KeyValueList⟩ } ⟧
    ;

  // Helper to describe actual list of arguments of function call.
  sort ExpressionList | ⟦ ⟨Expression⟩ ⟨ExpressionListTail⟩ ⟧  |  ⟦⟧ ;
  sort ExpressionListTail | ⟦ , ⟨Expression⟩ ⟨ExpressionListTail⟩ ⟧  |  ⟦⟧ ;

  // Helper to describe list of key-value pairs.
  sort KeyValueList  |  ⟦ ⟨KeyValue⟩ ⟨KeyValueListTail⟩ ⟧  |  ⟦⟧ ;
  sort KeyValueListTail   |  ⟦ , ⟨KeyValue⟩ ⟨KeyValueListTail⟩ ⟧  |  ⟦⟧ ;
  sort KeyValue       |  ⟦ ⟨IDENTIFIER⟩ : ⟨Expression⟩ ⟧ ;

  // TYPES ([1]1.3).
  //
  // Covers the cases of Figure 2.

  sort Type
    |  ⟦ boolean ⟧
    |  ⟦ number ⟧
    |  ⟦ string ⟧
    |  ⟦ void ⟧
    |  ⟦ ⟨IDENTIFIER⟩ ⟧
    |  ⟦ ( ⟨TypeList⟩ ) => ⟨Type⟩ ⟧
    |  ⟦ { ⟨NameTypeList⟩ } ⟧
    ;

  // Helper to describe list of types of arguments of function call.
  sort TypeList | ⟦ ⟨Type⟩ ⟨TypeListTail⟩ ⟧ |  ⟦⟧ ;
  sort TypeListTail | ⟦ , ⟨Type⟩ ⟨TypeListTail⟩ ⟧ | ⟦⟧ ;

  // Helper to describe list of names with types.
  sort NameTypeList  |  ⟦ ⟨NameType⟩ ⟨NameTypeListTail⟩ ⟧  |  ⟦⟧ ;
  sort NameTypeListTail   |  ⟦ , ⟨NameType⟩ ⟨NameTypeListTail⟩ ⟧  |  ⟦⟧ ;
  sort NameType       |  ⟦ ⟨IDENTIFIER⟩ : ⟨Type⟩ ⟧ ;

  // STATEMENTS ([1]1.4)
  //
  // Cases from Figure 3. Dangling else handled with LL order trick from class slides.

  sort Statement
    |  ⟦ { ⟨Statements⟩ } ⟧
    |  ⟦ var ⟨NameType⟩ ; ⟧
    |  ⟦ ⟨Expression⟩ ; ⟧
    |  ⟦ ; ⟧
    |  ⟦ if ( ⟨Expression⟩ ) ⟨IfTail⟩ ⟧
    |  ⟦ while ( ⟨Expression⟩ ) ⟨Statement⟩ ⟧
    |  ⟦ return ⟨Expression⟩ ; ⟧
    |  ⟦ return ; ⟧
    ;
  sort Statements | ⟦ ⟨Statement⟩ ⟨Statements⟩ ⟧   |  ⟦⟧ ;

  sort IfTail | ⟦ ⟨Statement⟩ else ⟨Statement⟩ ⟧  | ⟦ ⟨Statement⟩ ⟧ ;  // eagerly consume elses

  // DECLARATIONS ([1]1.5).
  //
  // Straight encoding.
  
  sort Declaration
    |  ⟦ interface ⟨IDENTIFIER⟩ { ⟨Members⟩ } ⟧
    |  ⟦ function ⟨IDENTIFIER⟩ ⟨CallSignature⟩ { ⟨Statements⟩ } ⟧
    ;

  sort Member
    |  ⟦ ⟨IDENTIFIER⟩ : ⟨Type⟩ ; ⟧
    |  ⟦ ⟨IDENTIFIER⟩ ⟨CallSignature⟩ { ⟨Statements⟩ } ⟧
    ;
  sort Members  |  ⟦ ⟨Member⟩ ⟨Members⟩ ⟧    |  ⟦⟧ ;

  sort CallSignature  |  ⟦ ( ⟨NameTypeList⟩ ) : ⟨Type⟩ ⟧ ;

  // PROGRAM ([1]1.6).
  //
  // Straight encoding, using Unit for the combination of statements and declarations,
  // with at least one Unit. Program is main input sort.

  main sort Program  |  ⟦ ⟨Units⟩ ⟧ ;

  sort Units  |  ⟦ ⟨Unit⟩ ⟨Units⟩ ⟧  |  ⟦ ⟨Unit⟩ ⟧ ;
  sort Unit  |  ⟦ ⟨Declaration⟩ ⟧  |  ⟦ ⟨Statement⟩ ⟧ ;

  ////////////////////////////////////////////////////////////////////////
  // IMPLEMENTATION OF SYNTAX-DIRECTED DEFINITION
  //
  // [2] references are to the Pr2Rose-SDD.pdf solution.
  
  // BOOLEANS ([2]1.3).

  sort Bool | True | False;
  
  | scheme And(Bool, Bool);
  And(False, #2) → False;
  And(True, #2) → #2;
  
  | scheme Or(Bool,Bool);
  Or(False, #2) → #2;
  Or(True, #2) → True;

  | scheme Not(Bool);
  Not(False) → True;
  Not(True) → False;

  sort TypeCheckResult | ⟦OK⟧ | ⟦Fail⟧;

  // TUPLES ([2]1.4).
  // We avoid pairs and use syntax constructions instead:

  // - ⟨Symbol,Type⟩ pairs are represented using NameType.

  // VECTORS ([2]1.5).
  // We avoid vectors and use syntax constructions instead:

  // - Vectors of ⟨Symbol,Type⟩ are represented using NameTypeListTail.
  //   So ε is just ⟦⟧ and ∥ is implemented as follows:
  sort NameTypeListTail;
  | scheme AppendNTLT(NameTypeListTail, NameTypeListTail);
  AppendNTLT(⟦⟧, #2) → #2;
  AppendNTLT(⟦ , ⟨NameType#11⟩ ⟨NameTypeListTail#12⟩ ⟧, #2)
    → ⟦ , ⟨NameType#11⟩ ⟨NameTypeListTail AppendNTLT(#12, #2) ⟩ ⟧ ;

  sort TypeList | scheme MergeTTL(Type, TypeList);
  MergeTTL(#1, ⟦⟧) → ⟦ ⟨Type#1⟩ ⟧ ;
  MergeTTL(#1, #2) → ⟦ ⟨Type#1⟩ ⟨TypeListTail ConvertToTLT(#2)⟩ ⟧ ;

  sort TypeListTail | scheme ConvertToTLT(TypeList);
  ConvertToTLT(⟦⟧) → ⟦⟧ ;
  ConvertToTLT( ⟦ ⟨Type#1⟩ ⟨TypeListTail#2⟩⟧) → ⟦ , ⟨Type#1⟩ ⟨TypeListTail#2⟩ ⟧ ;
  
  
  // - The special notation  { name-type-pairs }  for a Type then becomes:
  sort Type | scheme MakeInterfaceType(NameTypeListTail);
  MakeInterfaceType(⟦⟧) → ⟦ { } ⟧;
  MakeInterfaceType(⟦ , ⟨NameType#1⟩ ⟨NameTypeListTail#2⟩ ⟧)
    → ⟦ { ⟨NameType#1⟩ ⟨NameTypeListTail#2⟩ } ⟧;

  // MAPS ([2]1.6).
  // We use HACS built-in environment attributes for maps, with the usual convention.
  // ...

  // NAMESPACES ([2]1.7).
  // Names are represented by the IDENTIFIER token.

  // - The special  !+sym  notation is handled by the following helper.
  sort Computed | scheme Bang(Computed);
  Bang(#) → ⟦ "!" @ # ⟧ ;
  
  // ATTRIBUTES ([2]1.8).
  attribute ↑ok(Bool);

  sort Program | ↑ok;
  sort Units | ↑ok;
  sort Unit | ↑ok;
  sort Declaration | ↑ok;
  sort Members | ↑ok;
  sort Member | ↑ok;
  sort Statements | ↑ok;
  sort Statement | ↑ok;
  sort NameType | ↑ok;
  sort IfTail | ↑ok;
  sort Expression | ↑ok;
  sort KeyValueList | ↑ok;
  sort KeyValueListTail | ↑ok;
  sort KeyValue | ↑ok;
  
  
  attribute ↑ts(TypeList);

  sort NameTypeList | ↑ts;
  sort NameTypeListTail | ↑ts;
  sort ExpressionList | ↑ts;
  sort ExpressionListTail | ↑ts;
  
  attribute ↑t(Type);

  sort CallSignature | ↑t;
  sort NameType | ↑t;
  sort Expression | ↑t;
  
  attribute ↑ds(NameTypeListTail);
  
  sort Declaration | ↑ds;
  sort Members | ↑ds;
  sort Member | ↑ds;
  sort NameTypeList | ↑ds;
  sort NameTypeListTail | ↑ds;
  sort NameType | ↑ds;
  sort CallSignature | ↑ds;
  sort Statement | ↑ds;
  sort Unit | ↑ds;
  sort Units | ↑ds;

  attribute ↑uds(NameTypeListTail);

  sort Unit | ↑uds;
  
  // use new syntactic sort to define list of member names [2]1.8
  sort IdList | ⟦ ⟨IDENTIFIER⟩ ⟨IdListTail⟩ ⟧ | ⟦⟧ ;

  sort IdListTail | ⟦ , ⟨IDENTIFIER⟩ ⟨IdListTail⟩ ⟧ | ⟦⟧;
  
  attribute ↑sids(IdListTail);

  sort KeyValue | ↑sids;

  attribute ↑srt(Type);

  sort CallSignature | ↑srt;

  attribute ↓irt(Type);

  attribute ↓iids(IdListTail);

  attribute ↓r{IDENTIFIER:Type};

  attribute ↓te{IDENTIFIER : Type};

  // SYNTAX-DIRECTED DEFINITION ([2]1.9).
  
  // Rules  for Program
  sort Program;
  
  // P → Us1  |   Us1.te = Extend(GlobalDefs, Us1.ds)
  sort TypeCheckResult | scheme Check(Program);
  // Append globalDefs with Usds and extend it into the type environment
  Check(⟦ ⟨Units#Us ↑ds(#Usds)⟩⟧) → CheckHelper(ProgramSynOk(ExtendUsDsP(#Us, AppendNTLT(GlobalDefs, #Usds))));

  sort TypeCheckResult | scheme CheckHelper(Program);
  CheckHelper(# ↑ok(True)) → ⟦OK⟧;
  CheckHelper(# ↑ok(False)) → ⟦Fail⟧;
 
  sort Program | scheme ExtendUsDsP(Units, NameTypeListTail) ↓te;
  ExtendUsDsP(#Us,  ⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ ⟧)
    → ExtendUsDsP(#Us, #3) ↓te{#1: #2};
  ExtendUsDsP(#Us, ⟦⟧) → ⟦ ⟨Units UnitsAddTe(#Us)⟩⟧;

  sort Program | scheme ProgramSynOk(Program);
  ProgramSynOk(⟦ ⟨Units#Us ↑ds(#ds) ↑ok(#ok)⟩⟧) → ⟦ ⟨Units#Us⟩⟧ ↑ok(And(DistinctFirst(#ds),#ok));

  // Rules for Units
  sort Units;

  // Us → U1 Us2  |  Us.ds = U1.ds || Us2.ds  |  Us.ok = U1.ok ∧ Us2.ok
  ⟦ ⟨Unit#1 ↑ds(#Uds)⟩ ⟨Units#2 ↑ds(#Usds)⟩ ⟧ ↑ds( AppendNTLT(#Uds,#Usds) );

  // Us → U1  |  Us.ds = U1.ds
  ⟦ ⟨Unit# ↑ds(#ds)⟩ ⟧ ↑ds(#ds);

  sort Units | scheme  UnitsAddTe(Units) ↓te;
  
  // U1.te = Us.te   |   Us2.te = Extend(Us.te, U1.uds)
  UnitsAddTe(⟦ ⟨Unit#1 ↑uds(#uds)⟩ ⟨Units#2⟩ ⟧ ↑#syn)
    → UnitsSynOk(⟦ ⟨Unit UnitAddTe(#1)⟩ ⟨Units ExtendUUDsUs(#2, #uds)⟩ ⟧ ↑#syn);
  // U1.te = Us.te
  UnitsAddTe(⟦ ⟨Unit#1⟩ ⟧ ↑#syn) →  UnitsSynOk(⟦ ⟨Unit UnitAddTe(#1)⟩⟧ ↑#syn);

  sort Units | scheme ExtendUUDsUs(Units, NameTypeListTail) ↓te;
  ExtendUUDsUs(#Us, ⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ ⟧)
    → ExtendUUDsUs(#Us, #3) ↓te{#1:#2};
  ExtendUUDsUs(#Us, ⟦⟧) →  UnitsAddTe(#Us);

  sort Units | scheme UnitsSynOk(Units) ↓te;
  UnitsSynOk(⟦ ⟨Unit#1 ↑ok(#ok1)⟩ ⟨Units#2 ↑ok(#ok2)⟩ ⟧ ↑#syn)
    → ⟦ ⟨Unit#1⟩ ⟨Units#2⟩ ⟧ ↑#syn ↑ok(And(#ok1,#ok2));
  UnitsSynOk(⟦ ⟨Unit#1 ↑ok(#ok)⟩ ⟧ ↑#syn) → ⟦ ⟨Unit#1⟩ ⟧ ↑#syn ↑ok(#ok);

  // Rules for Unit
  sort Unit;

  // U → D1  |  U.ds = D1.ds  |    |  U.uds = ε
  ⟦ ⟨Declaration# ↑ds(#Dds)⟩ ⟧ ↑ds(#Dds) ↑uds(⟦⟧);

  // U → S1  |  U.ds = ε  |  U.uds = S1.ds
  ⟦ ⟨Statement# ↑ds(#Sds)⟩ ⟧ ↑ds(⟦⟧)  ↑uds(#Sds);
  
  sort Unit | scheme UnitAddTe(Unit) ↓te;
  UnitAddTe( ⟦ ⟨Declaration#⟩ ⟧ ↑#syn) → UnitSynOk(⟦ ⟨Declaration DeclarationAddTe(#)⟩⟧ ↑#syn);
  UnitAddTe(⟦ ⟨Statement#⟩ ⟧ ↑#syn) → UnitSynOk(⟦ ⟨Statement StatementAddTe(#)⟩⟧ ↑#syn);

  sort Unit | scheme UnitSynOk(Unit) ↓te;
  UnitSynOk(⟦ ⟨Declaration# ↑ok(#ok)⟩ ⟧ ↑#syn) → ⟦ ⟨Declaration#⟩ ⟧ ↑#syn ↑ok(#ok);
  UnitSynOk(⟦ ⟨Statement# ↑ok(#ok)⟩ ⟧ ↑#syn) → ⟦ ⟨Statement#⟩ ⟧ ↑#syn ↑ok(#ok);
  
  // Rules for Delcaration.
  sort Declaration;

  // D → interface id1 { Ms2 }    |    D.ds = ( ⟨!+id1.sym, { Ms2.ds } ⟩ )
  ⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2 ↑ds(#Ms2ds)⟩ } ⟧
    ↑ds( ⟦ , ⟨IDENTIFIER Bang(⟦#1⟧)⟩ : ⟨Type MakeInterfaceType(#Ms2ds)⟩ ⟧ ) ;

  ⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑t(#Cst)⟩ { ⟨Statements#3⟩ } ⟧
    ↑ds(⟦ , ⟨IDENTIFIER#1⟩:⟨Type#Cst⟩  ⟧);

  sort Declaration | scheme DeclarationAddIrt(Declaration) ↓irt;
  DeclarationAddIrt(⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑srt(#srt)⟩ { ⟨Statements#3⟩ } ⟧ ↑#syn)
    → DeclarationSynOk(⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2⟩ { ⟨Statements StatementsAddIrt(#3) ↓irt(#srt)⟩ } ⟧ ↑#syn);
  default DeclarationAddIrt(#) → DeclarationSynOk(#);
  
  sort Declaration | scheme DeclarationAddTe(Declaration) ↓te;     
  DeclarationAddTe(⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2⟩ } ⟧ ↑#syn)
    → DeclarationSynOk(⟦interface ⟨IDENTIFIER#1⟩ { ⟨Members MembersAddTe(#2)⟩ }⟧ ↑#syn);
  DeclarationAddTe(⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#ds)⟩ { ⟨Statements#3⟩ } ⟧ ↑#syn)
    → DeclarationSynOk(⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#ds)⟩ { ⟨Statements ExtendCsDsSs(#3, #ds)⟩ } ⟧ ↑#syn);

  sort Statements | scheme ExtendCsDsSs(Statements, NameTypeListTail) ↓te;
  ExtendCsDsSs(#Ss, ⟦⟧) → StatementsAddTe(#Ss);
  ExtendCsDsSs(#Ss, ⟦, ⟨IDENTIFIER#21⟩:⟨Type#22⟩ ⟨NameTypeListTail#23⟩⟧ )
	 → ExtendCsDsSs(#Ss, #23) ↓te{#21:#22};

  sort Declaration | scheme DeclarationSynOk(Declaration) ↓te ↓irt;
  DeclarationSynOk(⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#ds)⟩ { ⟨Statements#3 ↑ok(#ok)⟩ } ⟧ ↑#syn)
    → ⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2⟩ { ⟨Statements#3⟩ } ⟧ ↑#syn ↑ok(And(DistinctFirst(#ds),#ok));
  DeclarationSynOk(⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2 ↑ds(#ds) ↑ok(#ok2)⟩ } ⟧ ↑#syn)
    → ⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2⟩ } ⟧ ↑#syn ↑ok(And(DistinctFirst(#ds),#ok2));
  
  // Rules for Ms.
  sort Members;
  
  // Ms → M1 Ms2    |    M.ds = M1.ds || Ms2.ds  |  Ms.ok = M1.ok ∧ Ms2.ok
  ⟦ ⟨Member#1 ↑ds(#M1ds)⟩ ⟨Members#2↑ds(#Ms2ds)⟩ ⟧ ↑ds( AppendNTLT(#M1ds, #Ms2ds) );

  // Ms → ε    |    Ms.ds = ε
  ⟦⟧ ↑ds( ⟦⟧ );
  
  sort Members | scheme MembersAddTe(Members) ↓te;
  MembersAddTe( ⟦ ⟨Member#1⟩ ⟨Members#2⟩ ⟧ ↑#syn)
    → MembersSynOk(⟦⟨Member MemberAddTe(#1)⟩ ⟨Members MembersAddTe(#2)⟩⟧ ↑#syn);
  default MembersAddTe(#) → MembersSynOk(#);

  sort Members | scheme MembersSynOk(Members) ↓te;
  MembersSynOk(⟦ ⟨Member#1 ↑ok(#ok1)⟩ ⟨Members#2 ↑ok(#ok2)⟩ ⟧ ↑#syn)
    →  ⟦ ⟨Member#1⟩ ⟨Members#2⟩ ⟧ ↑#syn ↑ok(And(#ok1,#ok2));
  MembersSynOk(⟦⟧) → ⟦⟧ ↑ok(True);
  
  // Rules for M.
  sort Member;

  // M → id1 : T2  |  M.ds = ⟨id1.sym, T2⟩  |  M.ok = True
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧ ↑ds( ⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟧ );

  // M → id1 CS2 {Ss3}  |  M.ds = ⟨id1.sym, CS2.t⟩  |  M.ok = DistinctFirst(CS2.ds) ∧ Ss3.ok
  ⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑t(#Cst)⟩ { ⟨Statements#3⟩ } ⟧
    ↑ds(⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#Cst⟩⟧);
  
  sort Member | scheme MemberAddTe(Member) ↓te;
  MemberAddTe(⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#ds)⟩ { ⟨Statements#3⟩ } ⟧ ↑#syn)
    → MemberSynOk(⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#ds)⟩ { ⟨Statements ExtendCsDsSs(#3, #ds)⟩ } ⟧ ↑#syn);
  default MemberAddTe(#) → MemberSynOk(#);

  sort Member | scheme MemberSynOk(Member) ↓te;
  MemberSynOk(⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#ds)⟩ { ⟨Statements#3 ↑ok(#ok3)⟩ } ⟧ ↑#syn)
    → ⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2⟩ { ⟨Statements#3⟩ } ⟧ ↑#syn ↑ok(And(DistinctFirst(#ds),#ok3));
  MemberSynOk(⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧) → ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧ ↑ok(True);
	    
  // Rules for CS   |   CS → (NTL1) : T2
  sort CallSignature;
  
  // CS.ds = NTL1.ds  |  CS.t = (NTL1.ts)=>T2  |  CS.rt = T2
  ⟦ ( ⟨NameTypeList#1 ↑ds(#NTLds) ↑ts(#NTLts)⟩ ) : ⟨Type#2⟩ ⟧
    ↑ds( #NTLds ) ↑t( ⟦ ( ⟨TypeList #NTLts⟩ ) => ⟨Type#2⟩ ⟧ ) ↑srt(⟦⟨Type#2⟩⟧);

   // Rules for NTL  |  NTL → NT1 NTLT2  |  NTL → ε
  sort NameTypeList;

  // NTL.ds = NT1.ds || NTLT2.ds   |   NTL.ts = NT1.t || NTLT2.ts
  ⟦ ⟨NameType#1 ↑ds(#NTds) ↑t(#NTt)⟩ ⟨NameTypeListTail#2 ↑ds(#NTLTds) ↑ts(#NTLTts)⟩ ⟧
    ↑ds(AppendNTLT(#NTds, #NTLTds)) ↑ts(MergeTTL(#NTt, #NTLTts)) ;

  // NT.ds = ε
  ⟦⟧ ↑ds( ⟦⟧ ) ↑ts(⟦⟧);

  // Rules for NTLT
  sort NameTypeListTail;

  //  NTLT → , NT1 NTLT2   |   NTLT.ds = NT1.ds || NTLT2.ds
  ⟦ , ⟨NameType#1 ↑ds(#NTds) ↑t(#NTt)⟩ ⟨NameTypeListTail#2 ↑ds(#NTLTds) ↑ts(#NTLTts)⟩ ⟧
    ↑ds(AppendNTLT(#NTds,#NTLTds)) ↑ts( MergeTTL(#NTt, #NTLTts) );

  // NTLT → ε  |   NTLT.ds =  ε  | NTLT.ts = ε
  ⟦⟧ ↑ds( ⟦⟧ ) ↑ts( ⟦⟧ ) ;

  // Rules for NT   |    NT → id1 : T2;
  sort NameType;

  // NT.ds = (⟨id1.sym, T2⟩)  |  NT.t = T2
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟧ ↑ds( ⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟧ ) ↑t(#2);

  // Rules for Ss
  sort Statements;
  
  sort Statements | scheme StatementsAddIrt(Statements) ↓irt;
  StatementsAddIrt(⟦ ⟨Statement #1⟩ ⟨Statements#2⟩ ⟧ ↑#syn)
    → StatementsSynOk(⟦ ⟨Statement#1⟩ ⟨Statements StatementsAddIrt(#2)⟩ ⟧ ↑#syn);
  default StatementsAddIrt(#) → #;

  sort Statements | scheme StatementsAddTe(Statements) ↓te;
  StatementsAddTe( ⟦ ⟨Statement#1 ↑ds(#ds)⟩ ⟨Statements#2⟩ ⟧ ↑#syn)
    →  StatementsSynOk(⟦ ⟨Statement StatementAddTe(#1)⟩ ⟨Statements ExtendSDsSs(#2, #ds)⟩ ⟧ ↑#syn); 
  default StatementsAddTe(⟦⟧ ↑#syn)  → StatementsSynOk(⟦⟧ ↑#syn);

  sort Statements | scheme ExtendSDsSs(Statements, NameTypeListTail) ↓te;
  ExtendSDsSs(#Ss,  ⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ ⟧)
	    → ExtendSDsSs(#Ss, #3) ↓te{#1:#2};
  ExtendSDsSs(#Ss, ⟦⟧) → StatementsAddTe(#Ss);

  sort Statements | scheme StatementsSynOk(Statements) ↓irt ↓te;
  StatementsSynOk(⟦ ⟨Statement#1 ↑ok(#ok1)⟩ ⟨Statements#2 ↑ok(#ok2)⟩ ⟧ ↑#syn)
    → ⟦ ⟨Statement #1⟩ ⟨Statements#2⟩ ⟧ ↑#syn ↑ok(And(#ok1,#ok2));
  StatementsSynOk(#) → # ↑ok(True);

  // Rules for S  
  sort Statement;
  
  // attribute ↑ds
  ⟦ { ⟨Statements#⟩ } ⟧ ↑ds(⟦⟧);
  ⟦ var ⟨NameType# ↑ds(#NTds)⟩ ; ⟧ ↑ds(#NTds) ;
  ⟦ ⟨Expression#⟩ ; ⟧ ↑ds(⟦⟧);
  ⟦ ; ⟧ ↑ds(⟦⟧);
  ⟦ if ( ⟨Expression#1⟩ ) ⟨IfTail#2⟩ ⟧ ↑ds(⟦⟧) ;
  ⟦ while ( ⟨Expression#1⟩ ) ⟨Statement#2⟩ ⟧ ↑ds(⟦⟧) ;
  ⟦ return ⟨Expression#⟩ ; ⟧ ↑ds(⟦⟧) ;
  ⟦ return ; ⟧ ↑ds(⟦⟧) ;
       
  sort Statement | scheme StatementAddTe(Statement) ↓te;
  StatementAddTe( ⟦ { ⟨Statements#⟩ } ⟧ ↑#syn)
    → StatementSynOk(⟦ { ⟨Statements StatementsAddTe(#)⟩ } ⟧ ↑#syn);
  StatementAddTe( ⟦ ⟨Expression#⟩ ; ⟧ ↑#syn)
    → StatementSynOk(⟦ ⟨Expression ExpressionAddTe(#)⟩ ; ⟧ ↑#syn);
  StatementAddTe( ⟦ if ( ⟨Expression#1⟩ ) ⟨IfTail#2⟩ ⟧ ↑#syn)
    → StatementSynOk(⟦if ( ⟨Expression ExpressionAddTe(#1)⟩ ) ⟨IfTail IfTailAddTe(#2)⟩⟧ ↑#syn);
  StatementAddTe( ⟦ while ( ⟨Expression#1⟩ ) ⟨Statement#2⟩ ⟧ ↑#syn)
    → StatementSynOk(⟦ while ( ⟨Expression ExpressionAddTe(#1)⟩ ) ⟨Statement StatementAddTe(#2)⟩ ⟧ ↑#syn);
  StatementAddTe( ⟦ return ⟨Expression#⟩ ; ⟧ ↑#syn)
    → StatementSynOk(⟦ return ⟨Expression ExpressionAddTe(#)⟩ ;⟧ ↑#syn);
  default StatementAddTe(#) → StatementSynOk(#);

  sort Statement | scheme StatementAddIrt(Statement) ↓irt;
  StatementAddIrt( ⟦ { ⟨Statements#⟩ } ⟧ ↑#syn)
    → StatementSynOk(⟦ { ⟨Statements StatementsAddIrt(#)⟩ } ⟧ ↑#syn);
  StatementAddIrt( ⟦ while ( ⟨Expression#1⟩ ) ⟨Statement#2⟩ ⟧ ↑#syn)
    → StatementSynOk(⟦ while ( ⟨Expression#1⟩ ) ⟨Statement StatementAddIrt(#2)⟩ ⟧ ↑#syn);
  StatementAddIrt( ⟦ return ⟨Expression#⟩ ; ⟧ ↑#syn)
    → StatementSynOk(⟦ return ⟨Expression#⟩ ;⟧ ↑#syn);
  default StatementAddIrt(#) → StatementSynOk(#);

  sort Statement | scheme StatementSynOk(Statement) ↓te ↓irt;
  StatementSynOk(⟦ { ⟨Statements# ↑ok(#ok1)⟩ } ⟧ ↑#syn) → ⟦ { ⟨Statements#⟩ } ⟧ ↑#syn ↑ok(#ok1);
  StatementSynOk(⟦ var ⟨NameType# ↑t(#t1)⟩ ; ⟧) → ⟦ var ⟨NameType#⟩ ; ⟧ ↑ok(Eq(#t1,#t1));
  StatementSynOk(⟦ ⟨Expression# ↑ok(#ok)⟩ ; ⟧ ↑#syn) → ⟦ ⟨Expression#⟩ ; ⟧ ↑#syn ↑ok(#ok);
  StatementSynOk(⟦ if ( ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ ) ⟨IfTail#2 ↑ok(#ok2)⟩ ⟧ ↑#syn)
    → ⟦ if ( ⟨Expression#1⟩ ) ⟨IfTail#2⟩ ⟧ ↑#syn ↑ok(And(Eq(⟦boolean⟧,#t1),And(#ok1,#ok2)));
  StatementSynOk(⟦ while ( ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ ) ⟨Statement#2 ↑ok(#ok2)⟩ ⟧ ↑#syn)
    → ⟦ while ( ⟨Expression#1⟩ ) ⟨Statement#2⟩ ⟧ ↑#syn ↑ok(And(And(#ok1,#ok2),Eq(⟦boolean⟧,#t1)));
  StatementSynOk(⟦ return ⟨Expression#⟩ ; ⟧ ↑#syn)
    →  ⟦ return ⟨Expression#⟩ ; ⟧ ↑#syn ↑ok(True);
  StatementSynOk(⟦ return ; ⟧) → ⟦ return ; ⟧ ↑ok(True);
  StatementSynOk(⟦ ; ⟧) → ⟦ ; ⟧ ↑ok(True);

  // Rules for IT
  sort IfTail;

  sort IfTail | scheme IfTailAddTe(IfTail)↓te;
  IfTailAddTe( ⟦ ⟨Statement#1⟩ else ⟨Statement#2⟩ ⟧ ↑#syn)
	    → ⟦ ⟨Statement StatementAddTe(#1)⟩ else ⟨Statement StatementAddTe(#2)⟩ ⟧ ↑#syn;
  IfTailAddTe(⟦ ⟨Statement#⟩ ⟧ ↑#syn) → ⟦⟨Statement StatementAddTe(#)⟩⟧ ↑#syn;

  sort IfTail | scheme IfTailSynOk(IfTail) ↓te;
  IfTailSynOk(⟦ ⟨Statement#1 ↑ok(#ok1)⟩ else ⟨Statement#2 ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Statement#1⟩ else ⟨Statement#2⟩ ⟧ ↑ok(And(#ok1,#ok2));
  IfTailSynOk(⟦ ⟨Statement#⟩ ⟧ ↑#syn) → ⟦ ⟨Statement#⟩ ⟧ ↑ok(True);

  // Rules for E
  sort Expression;

  // E → str1  |  E.t = string  |  E.ok = True
  ⟦ ⟨STRING#⟩ ⟧ ↑t(⟦string⟧);
  
  // E → int1  |  E.t = number  |  E.ok = True
  ⟦ ⟨INTEGER#⟩ ⟧ ↑t(⟦number⟧);

  // E → ! E1  |  E.t = boolean  |  E.ok = E1.ok ∧ Eq(E.te, boolean, E1.t)
  ⟦ ! ⟨Expression#⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E → ~ E1  |  E.t = number
  ⟦ ~ ⟨Expression#⟩ ⟧ ↑t(⟦number⟧) ;

  // E → -E1  |  E.t = number
  ⟦ - ⟨Expression#⟩ ⟧ ↑t(⟦number⟧) ;
  
  // E → +E1  |  E.t = number
  ⟦ + ⟨Expression#⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 * E2  |  E.t = number
  ⟦ ⟨Expression#1⟩ * ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 / E2  |  E.t = number
  ⟦ ⟨Expression#1⟩ / ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 % E2  |  E.t = number
  ⟦ ⟨Expression#1⟩ % ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 + E2  |  E.t = (Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t))?number : string
  //  ⟦ ⟨Expression@9⟩ + ⟨Expression@10⟩ ⟧

  // E → E1 − E2  |  E.t = number
  ⟦ ⟨Expression#1⟩ - ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E→E1 <=E2  |  E.t = boolean
  ⟦ ⟨Expression#1⟩ <= ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E→E1 >=E2  |  E.t = boolean
  ⟦ ⟨Expression#1⟩ >= ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E→E1 <E2  |  E.t = boolean
  ⟦ ⟨Expression#1⟩ < ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E→E1 >E2  |  E.t = boolean
  ⟦ ⟨Expression#1⟩ > ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E→E1 ==E2  |  E.t = boolean
  ⟦ ⟨Expression#1⟩ == ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E→E1 !=E2  |  E.t = boolean
  ⟦ ⟨Expression#1⟩ != ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E → E1 & E2  |  E.t = number
  ⟦ ⟨Expression#1⟩ & ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 | E2  |  E.t = number
  ⟦ ⟨Expression#1⟩ ^ ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ; 
   
  // E → E1 | E2  |  E.t = number
  ⟦ ⟨Expression#1⟩ | ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 && E2  |  E.t = boolean
  ⟦ ⟨Expression#1⟩ && ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E→E1 ∥E2  |  E.t = boolean
  ⟦ ⟨Expression#1⟩ || ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E→E1?E2 :E3  |  E.t = E2.t
  ⟦ ⟨Expression#1⟩ ? ⟨Expression#2 ↑t(#t2)⟩ : ⟨Expression#3⟩ ⟧ ↑t(#t2) ;

  // E→E1 =E2  |  E.t = E1.t
  ⟦ ⟨Expression#1 ↑t(#t1)⟩ = ⟨Expression#2⟩ ⟧ ↑t(#t1) ;

  // E→E1 +=E2  |  E.t = E1.t
  ⟦ ⟨Expression#1 ↑t(#t1)⟩ += ⟨Expression#2⟩ ⟧ ↑t(#t1) ;
  
  // E→E1 ={KVL2 }  |  E.t = E1.t
  ⟦ ⟨Expression#1 ↑t(#t1)⟩ = { ⟨KeyValueList#2⟩ } ⟧ ↑t(#t1) ;

  sort Expression | scheme ExpressionAddTe(Expression) ↓te;
  ExpressionAddTe(⟦ ⟨IDENTIFIER#⟩ ⟧) ↓te{#:#t} → ExpresssionSynOk(⟦ ⟨IDENTIFIER#⟩ ⟧ ↑t(#t) );
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ . ⟨IDENTIFIER#2⟩ ⟧ ↑#syn)
    →  ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ . ⟨IDENTIFIER#2⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ ( ⟨ExpressionList#2⟩ ) ⟧ ↑#syn)
    →  ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ ( ⟨ExpressionList ExpressionListAddTe(#2)⟩ ) ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ! ⟨Expression#⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ! ⟨Expression ExpressionAddTe(#)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ~ ⟨Expression#⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ~ ⟨Expression ExpressionAddTe(#)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ - ⟨Expression#⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ - ⟨Expression ExpressionAddTe(#)⟩ ⟧ ↑#syn);
  ExpressionAddTe(⟦ + ⟨Expression#⟩ ⟧ ↑#syn)
    →ExpresssionSynOk( ⟦ + ⟨Expression ExpressionAddTe(#)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ * ⟨Expression#2⟩ ⟧ ↑#syn)
    →  ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ * ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe(⟦ ⟨Expression#1⟩ / ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ / ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe(⟦ ⟨Expression#1⟩ % ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ % ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ + ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ + ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ - ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ - ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ < ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ < ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ > ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ > ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ <= ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ <= ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ >= ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ >= ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ == ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ == ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ != ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ != ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ & ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ & ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ ^ ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ ^ ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ | ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ | ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ && ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ && ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ || ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ || ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe(⟦ ⟨Expression#1⟩ ? ⟨Expression#2⟩ : ⟨Expression#3⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ ? ⟨Expression ExpressionAddTe(#2)⟩ : ⟨Expression ExpressionAddTe(#3)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ = ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ = ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ += ⟨Expression#2⟩ ⟧ ↑#syn)
    → ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ += ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);
  ExpressionAddTe( ⟦ ⟨Expression#1⟩ = { ⟨KeyValueList#2⟩ } ⟧ ↑#syn)
    →  ExpresssionSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ = { ⟨KeyValueList KeyValueListAddTe(#2)⟩ } ⟧ ↑#syn);
  default ExpressionAddTe(#) → ExpresssionSynOk(#);

  sort Expression | scheme ExpresssionSynOk(Expression) ↓te;
  ExpresssionSynOk(#) → #↑ok(True);
  ExpresssionSynOk(⟦ ⟨STRING#1⟩ ⟧) → ⟦ ⟨STRING#1⟩ ⟧↑ok(True);
  ExpresssionSynOk(⟦ ⟨IDENTIFIER#1⟩ ⟧) → ⟦ ⟨IDENTIFIER#1⟩ ⟧↑ok(True);
  ExpresssionSynOk(⟦ ⟨INTEGER#⟩ ⟧) → ⟦ ⟨INTEGER#⟩ ⟧↑ok(True);
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#Et) ↑ok(#Eok)⟩ . ⟨IDENTIFIER#2⟩ ⟧) → ⟦ ⟨Expression#1⟩ . ⟨IDENTIFIER#2⟩ ⟧↑ok(And(#Eok, IsMember(#Et, #2)));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#Et) ↑ok(#Eok)⟩ ( ⟨ExpressionList#2 ↑ts(#ELts) ↑ok(#ELok)⟩ ) ⟧)
    → ⟦ ⟨Expression#1⟩ ( ⟨ExpressionList#2⟩ ) ⟧↑ok(And(IsArguments(#Et, #ELts), And(#Eok, #ELok)));
  ExpresssionSynOk(⟦ + ⟨Expression#1 ↑ok(#Eok) ↑t(#Et)⟩ ⟧) → ⟦ + ⟨Expression#1⟩ ⟧↑ok(And(#Eok, Eq(⟦number⟧, #Et)));
  ExpresssionSynOk(⟦ ! ⟨Expression#1 ↑ok(#Eok) ↑t(#Et)⟩ ⟧) → ⟦ ! ⟨Expression#1⟩ ⟧↑ok(And(#Eok, Eq(⟦boolean⟧, #Et)));
  ExpresssionSynOk(⟦ ~ ⟨Expression#1 ↑ok(#Eok) ↑t(#Et)⟩ ⟧) → ⟦ ~ ⟨Expression#1⟩ ⟧↑ok(And(#Eok, Eq(⟦number⟧, #Et)));
  ExpresssionSynOk(⟦ - ⟨Expression#1 ↑ok(#Eok) ↑t(#Et)⟩ ⟧) → ⟦ - ⟨Expression#1⟩ ⟧↑ok(And(#Eok, Eq(⟦number⟧, #Et)));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑ok(#ok1) ↑t(#t1)⟩ * ⟨Expression#2 ↑ok(#ok2) ↑t(#t2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ * ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Eq(⟦number⟧,#t1),Eq(⟦number⟧,#t2))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑ok(#ok1) ↑t(#t1)⟩ / ⟨Expression#2 ↑ok(#ok2) ↑t(#t2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ / ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Eq(⟦number⟧,#t1),Eq(⟦number⟧,#t2))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑ok(#ok1) ↑t(#t1)⟩ % ⟨Expression#2 ↑ok(#ok2) ↑t(#t2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ % ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Eq(⟦number⟧,#t1),Eq(⟦number⟧,#t2))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑ok(#ok1) ↑t(#t1)⟩ + ⟨Expression#2 ↑ok(#ok2) ↑t(#t2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ + ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Or(Eq(⟦number⟧,#t1),Eq(⟦string⟧,#t1)),Or(Eq(⟦number⟧,#t2),Eq(⟦string⟧, #t2)))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ - ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ - ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Eq(⟦number⟧,#t1),Eq(⟦number⟧,#t2))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ < ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ < ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Eq(#t1,#t2),Or(Eq(⟦number⟧,#t1),Eq(⟦string⟧,#t1)))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ > ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ > ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Eq(#t1,#t2),Or(Eq(⟦number⟧,#t1),Eq(⟦string⟧,#t1)))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ <= ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ <= ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Eq(#t1,#t2),Or(Eq(⟦number⟧,#t1),Eq(⟦string⟧,#t1)))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ >= ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ >= ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Eq(#t1,#t2),Or(Eq(⟦number⟧,#t1),Eq(⟦string⟧,#t1)))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ == ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ == ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1, #ok2),Eq(#t1,#t2)));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ != ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ != ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1, #ok2),Eq(#t1,#t2)));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ & ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ & ⟨Expression#2⟩ ⟧ ↑ok(And(And(#ok1,#ok2),And(Eq(⟦number⟧, #t1),Eq(⟦number⟧,#t2))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ ^ ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ ^ ⟨Expression#2⟩ ⟧ ↑ok(And(And(#ok1,#ok2),And(Eq(⟦number⟧, #t1),Eq(⟦number⟧,#t2))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ | ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ | ⟨Expression#2⟩ ⟧ ↑ok(And(And(#ok1,#ok2),And(Eq(⟦number⟧, #t1),Eq(⟦number⟧,#t2))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ && ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ && ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(Eq(⟦boolean⟧,#t1),Eq(⟦boolean⟧,#t2))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ || ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ || ⟨Expression#2⟩ ⟧ ↑ok(And(And(#ok1,#ok2),And(Eq(⟦boolean⟧,#t1),Eq(⟦boolean⟧,#t2))));
  ExpresssionSynOk( ⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ = ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ = ⟨Expression#2⟩ ⟧↑ok(And(And(#ok1,#ok2),And(IsLValue(#1),Eq(#t1,#t2))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ ? ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ : ⟨Expression#3 ↑t(#t3) ↑ok(#ok3)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ ? ⟨Expression#2⟩ : ⟨Expression#3⟩ ⟧↑ok(And(And(#ok1,#ok2),And(#ok3,And(Eq(⟦boolean⟧,#t1),Eq(#t2,#t3)))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑t(#t1) ↑ok(#ok1)⟩ += ⟨Expression#2 ↑t(#t2) ↑ok(#ok2)⟩ ⟧)
    → ⟦ ⟨Expression#1⟩ += ⟨Expression#2⟩ ⟧ ↑ok(And(And(IsLValue(#1),And(#ok1,#ok2)),Or(And(Eq(⟦number⟧,#t1),Eq(⟦number⟧,#t2)),And(Eq(⟦string⟧,#t1),Or(Eq(⟦string⟧,#t2),Eq(⟦number⟧,#t2))))));
  ExpresssionSynOk(⟦ ⟨Expression#1 ↑ok(#ok1)⟩ = { ⟨KeyValueList#2 ↑ok(#ok2)⟩ } ⟧)
    → ⟦ ⟨Expression#1⟩ = { ⟨KeyValueList#2⟩ } ⟧↑ok(And(IsLValue(#1),And(#ok1,#ok2)));   

  // Rules for ExpressionList
  sort ExpressionList;

  // EL → E1 ELT2  |  EL.ts = (E1.t) ∥ ELT2.ts
  ⟦ ⟨Expression#1 ↑t(#Et)⟩ ⟨ExpressionListTail#2 ↑ts(#Ets)⟩ ⟧ ↑ts(MergeTTL(#Et, #Ets));

  // EL → ε   |   EL.ts = ε
  ⟦⟧ ↑ts(⟦⟧);
						
  sort ExpressionList | scheme ExpressionListAddTe(ExpressionList) ↓te;
  ExpressionListAddTe(⟦⟧ ↑#syn) →  ExpressionListSynOk(⟦⟧);
  default ExpressionListAddTe(⟦ ⟨Expression#1⟩ ⟨ExpressionListTail#2⟩ ⟧ ↑#syn)
    → ExpressionListSynOk(⟦ ⟨Expression ExpressionAddTe(#1)⟩ ⟨ExpressionListTail ExpressionListTailAddTe(#2)⟩ ⟧ ↑#syn);

  sort ExpressionList | scheme ExpressionListSynOk(ExpressionList) ↓te;
  ExpressionListSynOk(⟦⟧) → ⟦⟧↑ok(True);
  ExpressionListSynOk(⟦ ⟨Expression#1 ↑ok(#ok1)⟩ ⟨ExpressionListTail#2 ↑ok(#ok2)⟩ ⟧ )
    → ⟦ ⟨Expression#1⟩ ⟨ExpressionListTail#2⟩ ⟧ ↑ok(And(#ok1, #ok2));
 
  // Rules for ExpressionListTail
  sort ExpressionListTail;

  // ELT → E1 ELT2  |  ELT.ts = (E1.t) ∥ ELT2.ts
  ⟦ , ⟨Expression#1 ↑t(#Et)⟩ ⟨ExpressionListTail#2 ↑ts(#Ets)⟩ ⟧ ↑ts(MergeTTL(#Et, #Ets));

  // ELT → ε  |  ELT.ts = ε
  ⟦⟧ ↑ts(⟦⟧);

  sort ExpressionListTail | scheme ExpressionListTailAddTe(ExpressionListTail) ↓te;
  ExpressionListTailAddTe(⟦⟧) →  ExpressionListTailSynOk(⟦⟧) ;
  default ExpressionListTailAddTe( ⟦ , ⟨Expression#1⟩ ⟨ExpressionListTail#2⟩ ⟧)
    → ExpressionListTailSynOk(⟦ , ⟨Expression ExpressionAddTe(#1)⟩ ⟨ExpressionListTail ExpressionListTailAddTe(#2)⟩ ⟧);

  sort ExpressionListTail | scheme ExpressionListTailSynOk(ExpressionListTail) ↓te;
  ExpressionListTailSynOk(⟦⟧ ↑#syn) → ⟦⟧ ↑ok(True);
  ExpressionListTailSynOk(⟦ , ⟨Expression#1 ↑ok(#ok1)⟩ ⟨ExpressionListTail#2 ↑ok(#ok2)⟩ ⟧↑#syn)
    → ⟦ , ⟨Expression#1⟩ ⟨ExpressionListTail#2⟩ ⟧ ↑ok(And(#ok1,#ok2));
  
  // Rules for KVL
  sort KeyValueList;

  sort KeyValueList | scheme KeyValueListAddIids(KeyValueList) ↓iids;
  KeyValueListAddIids(⟦⟧) → ⟦⟧;
  KeyValueListAddIids(⟦ ⟨KeyValue#1 ↑sids(#sids)⟩ ⟨KeyValueListTail#2⟩ ⟧ ↑#syn)
    → ⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail#2 ↓iids(#sids)⟩ ⟧ ↑#syn;

  sort KeyValueList | scheme KeyValueListAddR(KeyValueList) ↓r;
  KeyValueListAddR(⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧ ↑#syn) →
    ⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail KeyValueListTailAddR(#2)⟩ ⟧ ↑#syn;
  default KeyValueListAddR(#) → #;

  sort KeyValueList | scheme KeyValueListAddTe(KeyValueList) ↓te;
  KeyValueListAddTe(⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧ ↑#syn)
    → KeyValueListSynOk(⟦ ⟨KeyValue KeyValueAddTe(#1)⟩ ⟨KeyValueListTail KeyValueListTailAddTe(#2)⟩ ⟧ ↑#syn);
  default KeyValueListAddTe(⟦⟧ ↑#syn) →  KeyValueListSynOk(⟦⟧ ↑#syn);

  sort KeyValueList | scheme KeyValueListSynOk(KeyValueList) ↓te ↓iids;
  KeyValueListSynOk(⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧ ↑#syn)
    → ⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧ ↑#syn ↑ok(True);
  default KeyValueListSynOk(⟦⟧) → ⟦⟧ ↑ok(True);

  // Rules for KeyValueListTail
  sort KeyValueListTail;
  
  sort KeyValueListTail | scheme KeyValueListTailAddIids(KeyValueListTail) ↓iids;
  KeyValueListTailAddIids(⟦ , ⟨KeyValue#1 ↑sids(#sids)⟩ ⟨KeyValueListTail#2⟩ ⟧ ↑#syn)
    → ⟦ , ⟨KeyValue#1 ↑sids(#sids)⟩ ⟨KeyValueListTail#2 ↓iids(#sids)⟩ ⟧ ↑#syn;
  default KeyValueListTailAddIids(⟦⟧ ↑#syn) →⟦⟧ ↑#syn;
    
  sort KeyValueListTail | scheme KeyValueListTailAddR(KeyValueListTail) ↓r;
  KeyValueListTailAddR(⟦ , ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧ ↑#syn)
    → ⟦ , ⟨KeyValue#1⟩ ⟨KeyValueListTail KeyValueListTailAddR(#2)⟩ ⟧ ↑#syn;
  default KeyValueListTailAddR(⟦⟧) →  KeyValueListTailSynOk(⟦⟧);
						
  sort KeyValueListTail | scheme KeyValueListTailAddTe(KeyValueListTail) ↓te;
  KeyValueListTailAddTe(⟦ , ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧ ↑#syn)
    → KeyValueListTailSynOk(⟦ , ⟨KeyValue#1⟩ ⟨KeyValueListTail KeyValueListTailAddTe(#2)⟩ ⟧ ↑#syn);
  default KeyValueListTailAddTe(⟦⟧) → KeyValueListTailSynOk(⟦⟧);

  sort KeyValueListTail | scheme KeyValueListTailSynOk(KeyValueListTail) ↓r ↓iids ↓te;
  KeyValueListTailSynOk(⟦ , ⟨KeyValue#1 ↑sids(#sids)⟩ ⟨KeyValueListTail#2⟩ ⟧ ↑#syn)
     → ⟦ , ⟨KeyValue#1 ↑sids(#sids)⟩ ⟨KeyValueListTail#2⟩ ⟧↑#syn ↑ok(True);
  KeyValueListTailSynOk(⟦⟧ ↑#syn) →  ⟦⟧ ↑ok(True);

  // Rules for KV
  sort KeyValue;

  // KV → id1 : E2   |   KV.sids = (id1.sym)
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧ ↑sids(⟦, ⟨IDENTIFIER #1⟩ ⟧);

  sort KeyValue | scheme KeyValueAddTe(KeyValue) ↓te;
  KeyValueAddTe(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧ ↑#syn)
    → KeyValueSynOk(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression ExpressionAddTe(#2)⟩ ⟧ ↑#syn);

  sort KeyValue | scheme KeyValueSynOk(KeyValue);
  KeyValueSynOk(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2 ↑ok(#ok)⟩ ⟧ ↑#syn)
    → ⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2 ↑ok(#ok)⟩⟧↑#syn ↑ok(True);
  
  // SEMANTIC OPERATORS [2]1.11.
  
  sort NameTypeListTail | scheme GlobalDefs;
  GlobalDefs → ⟦ ,  document: {body: {innerHTML:string}} , length : (string)=>number, charAt: (string, number)=> number, substr:(string, number, number) => string⟧;
  
  sort Bool | scheme IsMember(Type, IDENTIFIER) ↓te; // ↓te{IDENTIFIER : Type}
  IsMember(⟦⟨IDENTIFIER#1⟩⟧, IDENTIFIER#2 ) ↓te{#1: #t} → True;
  IsMember(⟦ { ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ } ⟧, IDENTIFIER#1)
    → True;
  IsMember(⟦ boolean ⟧, IDENTIFIER#) → False;
  IsMember(⟦ number ⟧, IDENTIFIER#) → False;
  IsMember(⟦ string ⟧, IDENTIFIER#) → False;
  IsMember(⟦ void ⟧, IDENTIFIER#) → False;
  IsMember(⟦ ( ⟨TypeList#1⟩ ) => ⟨Type#2⟩ ⟧, IDENTIFIER#3) → False;
  IsMember(⟦ { } ⟧, IDENTIFIER#4)
    → False;
 default IsMember(⟦ { ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ } ⟧, IDENTIFIER#4)
    → IsMember(⟦ { ⟨NameTypeList ConvertNTLTtoNTL(#3)⟩ } ⟧ , IDENTIFIER#4);

  sort NameTypeList | scheme ConvertNTLTtoNTL(NameTypeListTail);
  ConvertNTLTtoNTL(⟦ , ⟨NameType#1⟩ ⟨NameTypeListTail#2⟩ ⟧ ) → ⟦ ⟨NameType#1⟩ ⟨NameTypeListTail#2⟩ ⟧ ;
  ConvertNTLTtoNTL(⟦⟧) → ⟦⟧;
  
  sort Type | scheme MemberType(Type, IDENTIFIER)↓te;
  MemberType(⟦ ⟨IDENTIFIER#⟩⟧, IDENTIFIER#)↓te{#:#t} → #t;
  MemberType(⟦ { ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ } ⟧, IDENTIFIER#1)
    → #2;
  default MemberType(⟦ { ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ } ⟧, IDENTIFIER#4)
    → MemberType(⟦ { ⟨NameTypeList ConvertNTLTtoNTL(#3)⟩ } ⟧, IDENTIFIER#4);

  sort Bool | scheme IsArguments(Type, TypeList) ↓te;
  IsArguments(⟦() => ⟨Type#1⟩⟧, ⟦⟧) → True;
  IsArguments(⟦(⟨Type#1⟩ ⟨TypeListTail#2⟩) => ⟨Type#3⟩⟧, ⟦⟧) → False;
  IsArguments(⟦() => ⟨Type#1⟩⟧, ⟦⟨Type#2⟩ ⟨TypeListTail#3⟩⟧) → False;
  IsArguments(⟦(⟨Type#1⟩ ⟨TypeListTail#2⟩) => ⟨Type#3⟩⟧, ⟦⟨Type#1⟩ ⟨TypeListTail#5⟩⟧)
    → IsArguments(⟦(⟨TypeList ConvertTLTtoTL(#2)⟩)=>⟨Type#3⟩⟧, ⟦⟨TypeList ConvertTLTtoTL(#5)⟩⟧);
  default IsArguments(⟦(⟨Type#1⟩ ⟨TypeListTail#2⟩) => ⟨Type#3⟩⟧, ⟦⟨Type#4⟩ ⟨TypeListTail#5⟩⟧)
    → And(Eq(#1, #4), IsArguments(⟦(⟨TypeList ConvertTLTtoTL(#2)⟩)=>⟨Type#3⟩⟧, ⟦⟨TypeList ConvertTLTtoTL(#5)⟩⟧));

  sort TypeList | scheme ConvertTLTtoTL(TypeListTail);
  ConvertTLTtoTL(⟦ , ⟨Type#1⟩ ⟨TypeListTail#2⟩ ⟧) → ⟦ ⟨Type#1⟩ ⟨TypeListTail#2⟩ ⟧;
  ConvertTLTtoTL(⟦⟧) → ⟦⟧;
  
  sort Type | scheme ReturnType(Type);
  ReturnType(⟦ ( ⟨TypeList#1⟩ ) => ⟨Type#2⟩ ⟧) → #2;
  default ReturnType(#) → error ⟦No return type found⟧;
  
  sort Bool | scheme Eq(Type, Type) ↓te;
  Eq(⟦ boolean ⟧,  ⟦ boolean ⟧) → True;
  [data #] Eq( ⟦ boolean ⟧, #) → EqHelper1(⟦boolean⟧,#);
  Eq(⟦ number ⟧,  ⟦ number ⟧) → True;
  [data #] Eq( ⟦ number ⟧, #) → EqHelper2(⟦ number ⟧, #);
  Eq(⟦ string ⟧,  ⟦ string ⟧) → True;
  [data #] Eq( ⟦ string ⟧, #) → EqHelper3(⟦ string⟧, #);
  Eq(⟦ void ⟧,  ⟦ void ⟧) → True;
  [data #] Eq( ⟦ void ⟧, #) → EqHelper4(⟦void⟧, #);
  Eq(⟦ ⟨IDENTIFIER#1⟩ ⟧ , ⟦ ⟨IDENTIFIER#2⟩ ⟧) ↓te{#n1:#1} ↓te{#n2:#2}→ Eq(#n1,#n2);
  Eq(⟦ ( ) => ⟨Type#13⟩ ⟧,  ⟦ ( ) => ⟨Type#13⟩ ⟧) → True;
  Eq(⟦ ( ) => ⟨Type#13⟩ ⟧,  ⟦ ( ) => ⟨Type#23⟩ ⟧) → False;
  Eq(⟦ ( ) => ⟨Type#13⟩ ⟧,  ⟦ ( ⟨Type#21⟩ ⟨TypeListTail#22⟩ ) => ⟨Type#23⟩ ⟧) → False;
  Eq(⟦ ( ⟨Type#11⟩ ⟨TypeListTail#12⟩ ) => ⟨Type#13⟩ ⟧,  ⟦ ( ) => ⟨Type#23⟩ ⟧) → False;
  default Eq(⟦ ( ⟨Type#11⟩ ⟨TypeListTail#12⟩ ) => ⟨Type#13⟩ ⟧,  ⟦ ( ⟨Type#21⟩ ⟨TypeListTail#22⟩ ) => ⟨Type#23⟩ ⟧)
    → And(Eq(#13, #23), And(Eq(#11,#21), Eq(⟦(⟨TypeList ConvertTLTtoTL(#12)⟩) => ⟨Type#13⟩⟧, ⟦(⟨TypeList ConvertTLTtoTL(#22)⟩) => ⟨Type#23⟩ ⟧)));
  Eq(⟦{ ⟨NameTypeList#1⟩ }⟧, ⟦{ ⟨NameTypeList#2⟩ }⟧) → And(EqHelper(#1,#2), EqHelper(#2,#1));

  sort Bool | scheme EqHelper1(Type, Type);
  EqHelper1(⟦ boolean ⟧,  ⟦ boolean ⟧) → True;
  EqHelper1(⟦boolean⟧,#) → False;

  sort Bool | scheme EqHelper2(Type, Type);
  EqHelper2(⟦ number ⟧, ⟦ number⟧) → True;
  EqHelper2(⟦ number ⟧, #) → False;

  sort Bool | scheme EqHelper3(Type, Type);
  EqHelper3(⟦ string ⟧,  ⟦ string ⟧) → True;
  EqHelper3( ⟦ string ⟧, #) → False;

  sort Bool | scheme EqHelper4(Type,Type);
  EqHelper4(⟦ void ⟧,  ⟦ void ⟧) → True;
  EqHelper4(⟦ void ⟧, #) → False;

  sort Bool | scheme EqHelper(NameTypeList, NameTypeList) ↓te;
  EqHelper(⟦⟧, ⟦⟧) → True;
  EqHelper(⟦⟧, ⟦⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#13⟩⟧) → True;
  EqHelper(⟦⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#13⟩⟧,⟦⟧) → False;
  default EqHelper(⟦⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#13⟩⟧,  ⟦⟨IDENTIFIER#21⟩ : ⟨Type#22⟩ ⟨NameTypeListTail#23⟩⟧)
    → And(IsInList(#11, #12, ⟦⟨IDENTIFIER#21⟩ : ⟨Type#22⟩ ⟨NameTypeListTail#23⟩⟧), EqHelper(⟦⟨NameTypeList ConvertNTLTtoNTL(#13)⟩⟧, ⟦⟨IDENTIFIER#21⟩ : ⟨Type#22⟩ ⟨NameTypeListTail#23⟩⟧));

  sort Bool | scheme IsInList(IDENTIFIER, Type, NameTypeList) ↓te;
  IsInList(#1, #2, ⟦⟧) → False;
  IsInList(#1, #2, ⟦⟨IDENTIFIER#1⟩ : ⟨Type#32⟩ ⟨NameTypeListTail#33⟩⟧)
    → Eq(#2, #32);
  default IsInList(#1, #2, ⟦⟨IDENTIFIER#31⟩ : ⟨Type#32⟩ ⟨NameTypeListTail#33⟩⟧)
    → IsInList(#1, #2, ⟦⟨NameTypeList ConvertNTLTtoNTL(#33)⟩⟧);

  sort Bool | scheme DistinctFirst(NameTypeListTail);
  DistinctFirst( ⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ ⟧ )
    → And(DistinctFirst(#3), DistinctFirstHelper(#1, #3));
  DistinctFirst( ⟦⟧ ) → True;

  sort Bool | scheme DistinctFirstHelper(IDENTIFIER, NameTypeListTail);
  DistinctFirstHelper(IDENTIFIER#1,  ⟦ , ⟨IDENTIFIER#21⟩ : ⟨Type#22⟩ ⟨NameTypeListTail#23⟩ ⟧)
    → And(IsDifferentIdentifier(#1, #21), DistinctFirstHelper(#1, #23));
  DistinctFirstHelper(IDENTIFIER#, ⟦⟧) → True;

  sort Bool | scheme IsDifferentIdentifier(IDENTIFIER, IDENTIFIER);
  IsDifferentIdentifier(#, #) → False;
  default IsDifferentIdentifier(#1, #2) → True;

  sort Bool | scheme IsEmpty(IdListTail);
  IsEmpty(⟦ , ⟨IDENTIFIER#1⟩ ⟨IdListTail#2⟩ ⟧) → False;
  IsEmpty(⟦⟧) → True;

  sort Bool | scheme IsLValue(Expression);
  IsLValue(⟦ ⟨IDENTIFIER#⟩ ⟧) → True;
  IsLValue(⟦ ⟨Expression#1⟩ . ⟨IDENTIFIER#2⟩ ⟧) → True;
  IsLValue(#) → False;
  
  // TESTS.

  // ---- Test for attribute ↑srt ----
  sort Type | scheme TestCallSignatureSrt(CallSignature);
  TestCallSignatureSrt(# ↑srt(#srt)) → #srt;

  // ---- Test for attribute ↑sids ----
  sort IdList | scheme TestKeyValueSids(KeyValue);
  TestKeyValueSids(# ↑sids(#sids)) → #sids;

  // ---- Test for attribute ↑uds ----
  sort NameTypeListTail | scheme TestUnitUds(Unit);
  TestUnitUds(#U ↑uds(#uds)) → #uds;

  //---- Test for attribute ↑ts ----
    
  // Testing ExpressionList↑ts
  sort TypeList | scheme TestExpressionListTs(ExpressionList);
  TestExpressionListTs(#EL ↑ts(#ELts)) → #ELts;

  // Testing ExpressionListTail↑ts
  sort TypeList | scheme TestExpressionListTailTs(ExpressionListTail);
  TestExpressionListTailTs(#ELT ↑ts(#ELTts)) → #ELTts;

  // Testing NameTypeList↑ts
  sort TypeList | scheme TestNameTypeListTs(NameTypeList);
  TestNameTypeListTs(#NTL ↑ts(#NTLts)) → #NTLts;

  //Testing NameTypeListTail↑ts
  sort TypeList | scheme TestNameTypeListTailTs(NameTypeListTail);
  TestNameTypeListTailTs(#NTLT ↑ts(#NTLTts)) → #NTLTts;

  //---- Test for attribute ↑t ----
  
  // Testing Expression ↑t
  sort Type | scheme TestExpressionT(Expression);
  TestExpressionT(# ↑t(#t)) → #t;

  // Testing CallSignature ↑t
  sort Type | scheme TestCallSignatureT(CallSignature);
  TestCallSignatureT(#CS ↑t(#t)) → #t;

  // Testing Nametype↑t
  sort Type | scheme TestNameTypeT(NameType);
  TestNameTypeT(#NT ↑t(#t)) → #t;

  //---- Test for attribute ↑ds ----
  
  // Testing Unit↑ds
  sort NameTypeListTail | scheme TestUnitDs(Unit);
  TestUnitDs(#U ↑ds(#ds)) → #ds;

  // Testing Units↑ds
  sort NameTypeListTail | scheme TestUnitsDs(Units);
  TestUnitsDs(#Us ↑ds(#ds)) → #ds;

  // Testing Statement↑ds
  sort NameTypeListTail | scheme TestStatementDs(Statement);
  TestStatementDs(#S ↑ds(#ds)) → #ds;

  // Testing CallSignature↑ds
  sort NameTypeListTail | scheme TestCallSignatureDs(CallSignature);
  TestCallSignatureDs(#CS ↑ds(#ds)) → #ds;

  // Testing NameTypeList↑ds
  sort NameTypeListTail | scheme TestNameTypeListDs(NameTypeList);
  TestNameTypeListDs(#NTL ↑ds(#ds)) → #ds;

  // Testing NameTypeListTail↑ds
  sort NameTypeListTail | scheme TestNameTypeListTailDs(NameTypeListTail);
  TestNameTypeListTailDs(#NTLT ↑ds(#ds)) → #ds;

  // Testing NameType↑ds:
  sort NameTypeListTail | scheme TestNameTypeDs(NameType);
  TestNameTypeDs(#NT ↑ds(#ds)) → #ds;

  // Testing Member↑ds
  sort NameTypeListTail | scheme TestMemberDs(Member);
  TestMemberDs(#M ↑ds(#ds)) → #ds;

  // Testing Members↑ds:
  sort NameTypeListTail | scheme TestMembersDs(Members);
  TestMembersDs(#Ms ↑ds(#ds)) → #ds;

  // Testing D↑ds:
  sort NameTypeListTail | scheme TestDeclarationDs(Declaration);
  TestDeclarationDs(#D ↑ds(#ds)) → #ds ;

  //---- Test for Helper scheme (taking more than two args) ----
  // ---- Test for Helper with one arg can be invoked directly by itself
  // define new syntactic sort to test IsMember
  sort TypeConsIdentifier | ⟦ ⟨Type⟩ : ⟨IDENTIFIER⟩ ⟧;

  sort Bool | scheme TestIsMember(TypeConsIdentifier);
  TestIsMember(⟦ ⟨Type#1⟩ : ⟨IDENTIFIER#2⟩ ⟧) → IsMember(#1,#2);

  sort Type | scheme TestMemberType(TypeConsIdentifier);
  TestMemberType(⟦ ⟨Type#1⟩ : ⟨IDENTIFIER#2⟩ ⟧) → MemberType(#1, #2);
  
  // define new syntactic sort to test Eq
  sort TypeConsType | ⟦ ⟨Type⟩:⟨Type⟩ ⟧;
  
  sort Bool | scheme TestEq(TypeConsType);
  TestEq(⟦ ⟨Type#1⟩:⟨Type#2⟩ ⟧) → Eq(#1, #2);

  // define new syntactic sort to test IsInList
  sort NameTypeConsNameTypeList | ⟦⟨NameType⟩:⟨NameTypeList⟩⟧;

  sort Bool | scheme TestIsInList(NameTypeConsNameTypeList);
  TestIsInList(⟦⟨IDENTIFIER#1⟩: ⟨Type#2⟩:⟨NameTypeList#3⟩⟧) → IsInList(#1, #2, #3);
  
  // define new syntactic sort to test IsArgument
  sort TypeConsTypeList | ⟦ ⟨Type⟩:⟨TypeList⟩ ⟧;
  
  sort Bool | scheme TestIsArguments(TypeConsTypeList);
  TestIsArguments(⟦ ⟨Type#1⟩:⟨TypeList#2⟩ ⟧) → IsArguments(#1, #2);

  // define new syntactic sort to test EqHelper
  sort NTLConsNTL | ⟦⟨NameTypeList⟩-⟨NameTypeList⟩⟧;

  sort Bool | scheme TestEqHelper(NTLConsNTL);
  TestEqHelper(⟦⟨NameTypeList#1⟩-⟨NameTypeList#2⟩⟧) → EqHelper(#1, #2);
  
}
