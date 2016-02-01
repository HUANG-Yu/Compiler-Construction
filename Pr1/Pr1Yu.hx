module edu.nyu.cs.Pr1Yu {
  /* LEXICAL ANALYSIS. */
  
  space [\ \t\n\r]
        | "//" .*
        | "/*" ( [^*] | '*' [^/] )* "*/"
        ;

  token INTEGER | ⟨Digit⟩+;

  token IDENTIFIER | ⟨IdPrefix⟩ (⟨IdPrefix⟩ | ⟨Digit⟩)*;

  token STRING | "\'" ( \\ ⟨Esc⟩ | [^\'\\\n] )* "\'"
               | "\"" ( \\ ⟨Esc⟩ | [^\"\\\n] )* "\""
               ;
  
  // \"\"  empty STRING

  token fragment Digit | [0-9];

  token fragment Letter | [a-zA-Z];

  token fragment IdPrefix | [$_]
	                  | ⟨Letter⟩
	                  ;

  token fragment Hex | [a-fA-F0-9];

  token fragment Esc | "\n"
                     |[^x]
	             | "x" ⟨Hex⟩ ⟨Hex⟩
	             ;
  
  /* SYNTAX ANALYSIS. */
  	 
  // Subscript Expressions
  sort Expression | ⟦ ⟨Expression@2⟩ = ⟨Expression@1⟩ ⟧@1
	          | ⟦ ⟨Expression@2⟩ += ⟨Expression@1⟩ ⟧@1
	          | ⟦ ⟨Expression@2⟩ = { ⟨ExpandEPair⟩ } ⟧@1
    
                  | ⟦ ⟨Expression@2⟩ ? ⟨Expression⟩ : ⟨Expression@3⟩⟧@2
    	 
	          | ⟦ ⟨Expression@3⟩ || ⟨Expression@4⟩ ⟧@3
    
	          | ⟦ ⟨Expression@4⟩ && ⟨Expression@5⟩ ⟧@4

	          | ⟦ ⟨Expression@5⟩ | ⟨Expression@6⟩ ⟧@5
    
	          | ⟦ ⟨Expression@6⟩ ^ ⟨Expression@7⟩ ⟧@6

	          | ⟦ ⟨Expression@7⟩ & ⟨Expression@8⟩ ⟧@7

	          | ⟦ ⟨Expression@8⟩ == ⟨Expression@9⟩ ⟧@8
	          | ⟦ ⟨Expression@8⟩ != ⟨Expression@9⟩ ⟧@8

	          | ⟦ ⟨Expression@9⟩ < ⟨Expression@10⟩ ⟧@9
	          | ⟦ ⟨Expression@9⟩ > ⟨Expression@10⟩ ⟧@9
	          | ⟦ ⟨Expression@9⟩ <= ⟨Expression@10⟩ ⟧@9
	          | ⟦ ⟨Expression@9⟩ >= ⟨Expression@10⟩ ⟧@9

	          | ⟦ ⟨Expression@10⟩ + ⟨Expression@11⟩ ⟧@10
	          | ⟦ ⟨Expression@10⟩ - ⟨Expression@11⟩ ⟧@10

	          | ⟦ ⟨Expression@11⟩ * ⟨Expression@12⟩ ⟧@11
	          | ⟦ ⟨Expression@11⟩ / ⟨Expression@12⟩ ⟧@11
	          | ⟦ ⟨Expression@11⟩ % ⟨Expression@12⟩ ⟧@11

	          | ⟦ ! ⟨Expression@12⟩ ⟧@12
	          | ⟦ ~ ⟨Expression@12⟩ ⟧@12
	          | ⟦ - ⟨Expression@12⟩ ⟧@12
	          | ⟦ + ⟨Expression@12⟩ ⟧@12

	          | ⟦ ⟨Expression@13⟩ (⟨ExpandE⟩) ⟧@13

	          | ⟦ ⟨Expression@14⟩ . ⟨Expression@15⟩ ⟧@14

	          | ⟦ ⟨IDENTIFIER⟩ ⟧@15
	          | ⟦ ⟨STRING⟩ ⟧@15
	          | ⟦ ⟨INTEGER⟩ ⟧@15
	          | ⟦ ( ⟨Expression⟩ ) ⟧@15 
	          ;


  sort ExpandEPair | ⟦ ⟧
	           | ⟦ ⟨EPairHead⟩ ⟨EPairTail⟩ ⟧
 	           ;
	 
  sort EPairHead | ⟦ ⟨IDENTIFIER⟩ : ⟨Expression⟩ ⟧; 

  sort EPairTail | ⟦ ⟧
	         | ⟦ , ⟨EPairHead⟩ ⟨EPairTail⟩ ⟧
 	         ;

  sort ExpandE | ⟦ ⟧
	       | ⟦ ⟨EHead⟩ ⟨ETail⟩ ⟧
	       ;
	 
  sort EHead | ⟦ ⟨Expression⟩ ⟧;

  sort ETail | ⟦ ⟧
	     | ⟦ , ⟨EHead⟩ ⟨ETail⟩ ⟧
	     ;
     
  //Subscript Types
  sort Type | ⟦ boolean ⟧
	    | ⟦ number ⟧
	    | ⟦ string ⟧
  	    | ⟦ void ⟧
	    | ⟦ ⟨IDENTIFIER⟩ ⟧
	    | ⟦ ( ⟨ExpandT⟩ ) => ⟨Type⟩ ⟧
	    | ⟦ { ⟨ExpandTPair⟩ } ⟧
	    ;
	 
  sort ExpandT | ⟦ ⟧
	       | ⟦ ⟨THead⟩ ⟨TTail⟩ ⟧
	       ;
	 
  sort THead | ⟦ ⟨Type⟩ ⟧;

  sort TTail | ⟦ ⟧
	     | ⟦ , ⟨THead⟩ ⟨TTail⟩ ⟧
	     ;

  sort ExpandTPair | ⟦ ⟧
	           | ⟦ ⟨TPairHead⟩ ⟨TPairTail⟩ ⟧
	           ;

  sort TPairHead | ⟦ ⟨IDENTIFIER⟩ : ⟨Type⟩ ⟧;

  sort TPairTail | ⟦ ⟧
	         | ⟦ , ⟨TPairHead⟩ ⟨TPairTail⟩ ⟧
	         ;
  
  // Subscript Statements
  sort Statement | ⟦ { ⟨Statements⟩ } ⟧
	         | ⟦ var ⟨IDENTIFIER⟩ : ⟨Type⟩ ; ⟧
	         | ⟦ ⟨Expression⟩ ; ⟧
	         | ⟦ ; ⟧
	         | ⟦ if ( ⟨Expression⟩ ) ⟨Statement⟩ else ⟨Statement⟩ ⟧
	         | ⟦ if ( ⟨Expression⟩ ) ⟨Statement⟩ ⟧
	         | ⟦ while ( ⟨Expression⟩ ) ⟨Statement⟩ ⟧
	         | ⟦ return ⟨Expression⟩ ; ⟧
                 | ⟦ return ; ⟧
	         ;

  sort Statements | ⟦ ⟧
	          | ⟦ ⟨Statement⟩ ⟨Statements⟩ ⟧
	          ;

  // Subscript Declarations
  sort Declaration | ⟦ ⟨InterfaceDeclaration⟩ ⟧
	           | ⟦ ⟨FunctionDeclaration⟩ ⟧
	           ;
	 
  sort InterfaceDeclaration | ⟦ interface ⟨IDENTIFIER⟩ { ⟨Members⟩ } ⟧;

  sort FunctionDeclaration | ⟦ function ⟨IDENTIFIER⟩ ⟨CallSignature⟩ { ⟨Statements⟩ } ⟧;

  sort Member | ⟦ ⟨IDENTIFIER⟩ : ⟨Type⟩ ; ⟧
	      | ⟦ ⟨IDENTIFIER⟩ ⟨CallSignature⟩ { ⟨Statements⟩ } ; ⟧
	      ;
	 
  sort CallSignature | ⟦ ( ⟨Parameter⟩ ) : ⟨Type⟩ ⟧;

  sort Parameter | ⟦ ⟧
	         | ⟦ ⟨ParameterHead⟩ ⟨ParameterTail⟩ ⟧
	         ;
	 
  sort ParameterHead | ⟦ ⟨IDENTIFIER⟩ : ⟨Type⟩ ⟧
                     // | ⟦ ⟨Type⟩ ⟨IDENTIFIER⟩⟧
                     ;

  sort ParameterTail | ⟦ ⟧
	             | ⟦ , ⟨ParameterHead⟩ ⟨ParameterTail⟩ ⟧
	             ;
	  
  sort Members | ⟦ ⟧
	       | ⟦ ⟨Member⟩ ⟨Members⟩ ⟧
	       ;

  /* MAIN */
  main sort Program | ⟦ ⟨Declarations⟩ ⟨Statement⟩ ⟨Statements⟩ ⟧;

  sort Declarations | ⟦ ⟧
	            | ⟦ ⟨Declaration⟩ ⟨Declarations⟩ ⟧
	            ;

  /* SEMANTIC SORTS & SCHEMES. */
}
