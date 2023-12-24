%{
#include <stdio.h>
#include <math.h>
#include <cstdio>
#include <list>
#include <iostream>
#include <string>
#include <memory>
#include <stdexcept>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/IRBuilder.h"

#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"

using namespace std;
using namespace llvm;  

struct matrix_dims{
  float rowSize;
  float colSize;
};

struct matrix_struct{
  matrix_dims dimens;
  vector<vector<Value*>*> *mat_vals;
};

struct var_imm_mat{ //either a var, imm, or matrix
  bool is_scalar;   // is not scalar, it's a matrix
  bool is_var;      // if not scalar, it is a var. if scalar, either var or not (literal result)
  char *var_nm;
  float fl_val;
  Value *var_val;
  matrix_struct mat_s;
};

#include "p1.y.hpp"
%}

/*%option debug*/

%%

[ \t\n]         /*ignore*/

return       { return RETURN; }
det          { return DET; }
transpose    { return TRANSPOSE; }
invert       { return INVERT; }
matrix       { return MATRIX; }
reduce       { return REDUCE; }
x            { return X; }  

[a-zA-Z_][a-zA-Z_0-9]* {  
                          char *tmp_s = (char*) malloc(strlen(yytext));
                          strcpy(tmp_s, yytext);
                          yylval.var_name = tmp_s;  
                          return ID; 
                        } 

[0-9]+        { 
                yylval.var_int = atoi(yytext);
                return INT; 
              }

[0-9]+("."[0-9]*) { 
                    yylval.var_float = atof(yytext);
                    return FLOAT; 
                  } 

"["           { return LBRACKET; }
"]"           { return RBRACKET; }
"{"           { return LBRACE; }
"}"           { return RBRACE; }
"("           { return LPAREN; }
")"           { return RPAREN; }

"="           { return ASSIGN; }
"*"           { return MUL; }
"/"           { return DIV; }
"+"           { return PLUS; }
"-"           { return MINUS; }

","           { return COMMA; }

";"           { return SEMI; }


"//".*\n      { }

.             { 
                return ERROR; 
              }
%%

//void printError(){
//  printf("Error - this input is not allowed!");
//}

int yywrap()
{
  return 1;
}