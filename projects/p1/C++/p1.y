%{
#include <cstdio>
#include <list>
#include <vector>
#include <map>
#include <iostream>
#include <fstream>
#include <string>
#include <memory>
#include <stdexcept>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"

#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/FileSystem.h"

using namespace llvm;
using namespace std;


// Need for parser and scanner
extern FILE *yyin;
int yylex();
void yyerror(const char*);
int yyparse();
 
// Needed for LLVM
string funName;
Module *M;
LLVMContext TheContext;
IRBuilder<> Builder(TheContext);


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

vector<string> theArgs;
int argsCnt = 0;

map<string, var_imm_mat> scalarVars;  //contains funcArgs + stmtVars
map<string, var_imm_mat> matVars; 

var_imm_mat mat_mat_div(var_imm_mat vim_mat1, var_imm_mat vim_mat2);
var_imm_mat mat_invert(var_imm_mat vim_expr);
var_imm_mat mat_transpose(var_imm_mat vim_expr);
var_imm_mat determinant(var_imm_mat vim_expr);
var_imm_mat internal_det_of_3x3(var_imm_mat vim_expr);
var_imm_mat mat_reduce(var_imm_mat vim_expr);
var_imm_mat mat_mat_mul(var_imm_mat vim_mat1, var_imm_mat vim_mat2);
var_imm_mat expr_expr_mul(var_imm_mat vim_expr1, var_imm_mat vim_expr2);
var_imm_mat expr_expr_div(var_imm_mat vim_expr1, var_imm_mat vim_expr2);
%}



%union {
  char *var_name; 
  int var_int;
  float var_float;
  struct var_imm_mat vim;
  struct matrix_dims mdims;
  struct matrix_struct m_struct;
  vector<vector<Value*>*> *vect_of_vect_of_Values;
  vector<Value*> *vect_of_Values;
}

%define parse.trace

%token ERROR

%token RETURN
%token DET TRANSPOSE INVERT
%token REDUCE
%token MATRIX
%token X

%token <var_name> ID
%token <var_int> INT
%token <var_float> FLOAT
%type <vim> expr

%token SEMI COMMA

%token PLUS MINUS MUL DIV
%token ASSIGN

%token LBRACKET RBRACKET
%token LPAREN RPAREN 
%token LBRACE RBRACE 

%type params_list

%type <vect_of_vect_of_Values> matrix_rows
%type <vect_of_Values> expr_list matrix_row
%type <mdims> dim

%left PLUS MINUS
%left MUL DIV 

%start program

%%

program: ID {
  funName = $1; 
} LPAREN params_list_opt RPAREN LBRACE statements_opt return RBRACE
{
  // parsing is done, input is accepted
  YYACCEPT;
}
;

params_list_opt:  params_list 
{
  std::vector<Type*> param_types(argsCnt,Builder.getFloatTy());  
  ArrayRef<Type*> Params (param_types);
  
  // Create int function type with no arguments
  FunctionType *FunType = 
    FunctionType::get(Builder.getFloatTy(),Params,false);

  // Create a main function
  Function *Function = Function::Create(FunType,GlobalValue::ExternalLinkage,funName,M);

  // LLVMCountParams(Function);

  int arg_no=0;
  for(auto &a: Function->args()) {
    Value *val = &a; 
    scalarVars[theArgs[arg_no]].var_val = val;
    arg_no++;

  }
  
  //Add a basic block to main to hold instructions, and set Builder
  //to insert there
  Builder.SetInsertPoint(BasicBlock::Create(TheContext, "entry", Function));
}
| %empty
{ 
  // Create int function type with no arguments
  FunctionType *FunType = 
    FunctionType::get(Builder.getFloatTy(),false);

  // Create a main function
  Function *Function = Function::Create(FunType,  
         GlobalValue::ExternalLinkage,funName,M);

  //Add a basic block to main to hold instructions, and set Builder
  //to insert there
  Builder.SetInsertPoint(BasicBlock::Create(TheContext, "entry", Function));
}
;

params_list: ID
{
  var_imm_mat vim_tmp;
  vim_tmp.is_var = true;
  vim_tmp.is_scalar = true;
  vim_tmp.var_nm = $1;
  scalarVars[$1] = vim_tmp;  
  theArgs.push_back($1);
  argsCnt++;
}
| params_list COMMA ID
{
  var_imm_mat vim_tmp;
  vim_tmp.is_var = true;
  vim_tmp.is_scalar = true;
  vim_tmp.var_nm = $3;
  scalarVars[$3] = vim_tmp;  
  theArgs.push_back($3);
  argsCnt++;
}
;

return: RETURN expr SEMI
{
  if($2.is_scalar){
    if($2.is_var){
      Builder.CreateRet(scalarVars[$2.var_nm].var_val);
    }else{
      Builder.CreateRet($2.var_val);
    }
  }else{
    yyerror("Cannot return a matrix");
    YYABORT;
  }
}
;

// These may be fine without changes
statements_opt: %empty
            | statements
;

// These may be fine without changes
statements:   statement
            | statements statement
;

statement: ID ASSIGN expr SEMI
{
  var_imm_mat vim_tmp;
  vim_tmp = $3; 
  vim_tmp.is_var = true;
  vim_tmp.var_nm = $1;

  if($3.is_scalar){
    //scalarVars[$1] = $3;
    scalarVars[$1] = vim_tmp;
  }else{
    //matVars[$1] = $3;
    matVars[$1] = vim_tmp;
  }
}
| ID ASSIGN MATRIX dim LBRACE matrix_rows RBRACE SEMI
{
  var_imm_mat vim_tmp;
  vim_tmp.is_scalar = false;
  vim_tmp.is_var = true;
  vim_tmp.var_nm = $1;
  vim_tmp.mat_s.dimens = $4;
  vim_tmp.mat_s.mat_vals = $6;  //matrix_rows AKA vector<vector<Value*>> *

  matVars[$1] = vim_tmp;
}
;

dim: LBRACKET INT X INT RBRACKET
{
  matrix_dims tmp_dims;
  tmp_dims.rowSize = $2;
  tmp_dims.colSize = $4;
  $$ = tmp_dims;
}
;

matrix_rows: matrix_row
{
  vector<vector<Value*>*> *tmp = new vector<vector<Value*>*>;
  tmp->push_back($1);
  $$ = tmp;
}
| matrix_rows COMMA matrix_row
{
  $1->push_back($3);
  $$ = $1;
}
;

matrix_row: LBRACKET expr_list RBRACKET
{
  $$ = $2;
}
;

expr_list: expr
{
  vector<Value*> *tmpV = new vector<Value*>;

  if(!$1.is_scalar){
    yyerror("Matrix elements can't reference other matrices");
    YYABORT;
  }
  
  if($1.is_var){
    if(scalarVars.count($1.var_nm) == 0){
      yyerror("Trying to use Undefined variable - expr_list ");
      YYABORT;
    }else{
      tmpV->push_back(scalarVars[$1.var_nm].var_val);
      $$ = tmpV;
    }
  }else{
    tmpV->push_back($1.var_val);
    $$ = tmpV;
  }
}
| expr_list COMMA expr
{
  if(!$3.is_scalar){
    yyerror("Matrix elements can't reference other matrices");
    YYABORT;
  }

  if($3.is_var){
    if(scalarVars.count($3.var_nm) == 0){
      yyerror("Trying to use Undefined variable - expr_list ");
      YYABORT;
    }else{
      $1->push_back(scalarVars[$3.var_nm].var_val);
    }
  }else{
    $1->push_back($3.var_val);
  }
  $$ = $1;
}
;

expr: ID
{
  if(scalarVars.count($1) > 0){
    $$ = scalarVars[$1]; 
  }else{
    if(matVars.count($1) > 0){
      $$ = matVars[$1];
      
    }else{
      yyerror("ERROR - Access to Undefined Variable");
      YYABORT;
    }
  }
}
| FLOAT
{
  var_imm_mat vim_tmp;
  vim_tmp.is_scalar = true;
  vim_tmp.is_var = false;
  vim_tmp.var_val = ConstantFP::get(Builder.getFloatTy(), $1);
  $$ =  vim_tmp;
}
| INT
{
  var_imm_mat vim_tmp;
  vim_tmp.is_scalar = true;
  vim_tmp.is_var = false;
  vim_tmp.var_val = ConstantFP::get(Builder.getFloatTy(), (float) $1);
  $$ =  vim_tmp;
}
| expr PLUS expr
{
  var_imm_mat vim_tmp;

  if($1.is_scalar){
    if(!$3.is_scalar){
      yyerror("Cannot add Scalar with Matrix 1");
      YYABORT;
    }
    if($1.is_var){
      if($3.is_var){
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFAdd(scalarVars[$1.var_nm].var_val, scalarVars[$3.var_nm].var_val, "fadd");
      }else{ 
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFAdd(scalarVars[$1.var_nm].var_val, $3.var_val, "fadd");
      }
    }else{
      if($3.is_var){
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFAdd($1.var_val, scalarVars[$3.var_nm].var_val , "fadd");
      }else{
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFAdd($1.var_val, $3.var_val, "fadd");
      }
    }

  }else{                                  //matrix add
    if($3.is_scalar){
      yyerror("Cannot add Scalar with Matrix 2");
      YYABORT;
    }

    vector<vector<Value*>*> *mat_rows = new vector<vector<Value*>*>;
    vector<Value*> *mat_cols;

    vim_tmp.is_scalar = false;
    vim_tmp.is_var = true;
    vim_tmp.mat_s.dimens.rowSize = matVars[$1.var_nm].mat_s.dimens.rowSize;
    vim_tmp.mat_s.dimens.colSize = matVars[$1.var_nm].mat_s.dimens.colSize;

    for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
      mat_cols = new vector<Value*>;
      for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
        mat_cols->push_back(Builder.CreateFAdd(matVars[$1.var_nm].mat_s.mat_vals->at(i)->at(j), matVars[$3.var_nm].mat_s.mat_vals->at(i)->at(j), "fadd"));
      }
      mat_rows->push_back(mat_cols);
    }
    char *tmpStr =(char*) "__in_place_mat_mat_add";
    vim_tmp.var_nm = tmpStr;              
    matVars[tmpStr] = vim_tmp;

    vim_tmp.mat_s.mat_vals = mat_rows;
  }

  $$ =  vim_tmp;
}
| expr MINUS expr
{
  var_imm_mat vim_tmp;

  if($1.is_scalar){
    if(!$3.is_scalar){
      yyerror("Cannot sub Scalar with Matrix 1");
      YYABORT;
    }

    if($1.is_var){
      if($3.is_var){
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFSub(scalarVars[$1.var_nm].var_val, scalarVars[$3.var_nm].var_val, "fsub");
      }else{ 
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFSub(scalarVars[$1.var_nm].var_val, $3.var_val, "fsub");
      }
    }else{
      if($3.is_var){
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFSub($1.var_val, scalarVars[$3.var_nm].var_val , "fsub");
      }else{
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFSub($1.var_val, $3.var_val, "fsub");
      }
    }

  }else{                                  //matrix sub
    if($3.is_scalar){
      yyerror("Cannot Substract Scalar with Matrix 2");
      YYABORT;
    }

    vector<vector<Value*>*> *mat_rows = new vector<vector<Value*>*>;
    vector<Value*> *mat_cols;

    vim_tmp.is_scalar = false;
    vim_tmp.is_var = true;
    vim_tmp.mat_s.dimens.rowSize = matVars[$1.var_nm].mat_s.dimens.rowSize;
    vim_tmp.mat_s.dimens.colSize = matVars[$1.var_nm].mat_s.dimens.colSize;

    for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
      mat_cols = new vector<Value*>;
      for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
        mat_cols->push_back(Builder.CreateFSub(matVars[$1.var_nm].mat_s.mat_vals->at(i)->at(j), matVars[$3.var_nm].mat_s.mat_vals->at(i)->at(j), "fsub"));
      }
      mat_rows->push_back(mat_cols);
    }

    vim_tmp.mat_s.mat_vals = mat_rows;

    char *tmpStr =(char*) "__in_place_mat_mat_sub";
    vim_tmp.var_nm = tmpStr;              
    matVars[tmpStr] = vim_tmp;
  }

  $$ =  vim_tmp;
}
| expr MUL expr
{
  $$ = expr_expr_mul($1, $3);
}
| expr DIV expr
{
  $$ = expr_expr_div($1, $3);
}
| MINUS expr
{
  var_imm_mat vim_tmp;

  if($2.is_scalar){
    vim_tmp.is_var = false;
    vim_tmp.is_scalar = true;
    if($2.is_var){
      vim_tmp.var_val = Builder.CreateFNeg(scalarVars[$2.var_nm].var_val, "fneg");
    }else{
      vim_tmp.var_val = Builder.CreateFNeg($2.var_val, "fneg");
    }
  }else{            // matrix negation
    vector<vector<Value*>*> *mat_rows = new vector<vector<Value*>*>;
    vector<Value*> *mat_cols;

    vim_tmp.is_scalar = false;
    vim_tmp.is_var = true;
    vim_tmp.mat_s.dimens.rowSize = matVars[$2.var_nm].mat_s.dimens.rowSize;
    vim_tmp.mat_s.dimens.colSize = matVars[$2.var_nm].mat_s.dimens.colSize;
  
    for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
      mat_cols = new vector<Value*>;
      for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
        mat_cols->push_back(Builder.CreateFNeg(matVars[$2.var_nm].mat_s.mat_vals->at(i)->at(j), "fneg"));
      }
      mat_rows->push_back(mat_cols);
    }
    vim_tmp.mat_s.mat_vals = mat_rows;

    char *tmpStr =(char*) "__in_place_negate";
    vim_tmp.var_nm = tmpStr;              
    matVars[tmpStr] = vim_tmp;
  }

  $$ =  vim_tmp;
}
| DET LPAREN expr RPAREN
{
  $$ = determinant($3);
}
| INVERT LPAREN expr RPAREN
{
  $$ = mat_invert($3);
}
| TRANSPOSE LPAREN expr RPAREN
{
  $$ = mat_transpose($3);
}
| ID LBRACKET INT COMMA INT RBRACKET
{
  if(matVars.count($1) == 0){
    yyerror("ERROR - Undefined Matrix Access");
    YYABORT;
  }

  if ($3 >= matVars[$1].mat_s.dimens.rowSize || $5 >= matVars[$1].mat_s.dimens.colSize){
    yyerror("ERROR - Out of Bounds Matrix Access");
    YYABORT;
  }

  var_imm_mat vim_tmp;
  vim_tmp.is_scalar = true;
  vim_tmp.is_var = false;
  vim_tmp.var_val = matVars[$1].mat_s.mat_vals->at($3)->at($5);

  $$ = vim_tmp;
}
| REDUCE LPAREN expr RPAREN
{
  $$ = mat_reduce($3);
}
| LPAREN expr RPAREN
{
  $$ = $2;
}
;

%%

var_imm_mat determinant(var_imm_mat vim_expr){

  if(vim_expr.is_scalar || !vim_expr.is_var){
    yyerror("ERROR - Can't get DETERMINANT of a non Matrix");
    //YYABORT; //TODO: yyabort instead of exit outside of yy rule parsing section???
    exit(EXIT_FAILURE);
  }
  if(matVars[vim_expr.var_nm].mat_s.dimens.rowSize != matVars[vim_expr.var_nm].mat_s.dimens.colSize){
    yyerror("ERROR - DETERMINANT cannot be found (MAT not square)");
    exit(EXIT_FAILURE);
  }
  
  var_imm_mat vim_tmp;
  vim_tmp.is_scalar = true;
  vim_tmp.is_var = false;

  if(matVars[vim_expr.var_nm].mat_s.dimens.rowSize == 1){

    vim_tmp.var_val = (* (*matVars[vim_expr.var_nm].mat_s.mat_vals)[0])[0];

  }else if(matVars[vim_expr.var_nm].mat_s.dimens.rowSize == 2){
    Value* tmpDet1, * tmpDet2, * tmpDet3;
    tmpDet1 = Builder.CreateFMul(matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(0), matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(1), "fmul");
    tmpDet2 = Builder.CreateFMul(matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(1), matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(0), "fmul");
    tmpDet3 = Builder.CreateFSub(tmpDet1, tmpDet2, "fsub");
    
    vim_tmp.var_val = tmpDet3;

  }else if(matVars[vim_expr.var_nm].mat_s.dimens.rowSize == 3){
    Value* tmpDet1, * tmpDet2, * tmpDet3, * tmpDet4, * tmpDet5, * tmpDet6, * tmpDet7;
    tmpDet1 = Builder.CreateFMul(matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(0), matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(1), "fmul");
    tmpDet2 = Builder.CreateFMul(tmpDet1, matVars[vim_expr.var_nm].mat_s.mat_vals->at(2)->at(2), "fmul");
    tmpDet1 = Builder.CreateFMul(matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(1), matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(2), "fmul");
    tmpDet3 = Builder.CreateFMul(tmpDet1, matVars[vim_expr.var_nm].mat_s.mat_vals->at(2)->at(0), "fmul");
    tmpDet1 = Builder.CreateFMul(matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(2), matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(0), "fmul");
    tmpDet4 = Builder.CreateFMul(tmpDet1, matVars[vim_expr.var_nm].mat_s.mat_vals->at(2)->at(1), "fmul");

    tmpDet1 = Builder.CreateFMul(matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(2), matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(1), "fmul");
    tmpDet5 = Builder.CreateFMul(tmpDet1, matVars[vim_expr.var_nm].mat_s.mat_vals->at(2)->at(0), "fmul");
    tmpDet1 = Builder.CreateFMul(matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(1), matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(0), "fmul");
    tmpDet6 = Builder.CreateFMul(tmpDet1, matVars[vim_expr.var_nm].mat_s.mat_vals->at(2)->at(2), "fmul");
    tmpDet1 = Builder.CreateFMul(matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(0), matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(2), "fmul");
    tmpDet7 = Builder.CreateFMul(tmpDet1, matVars[vim_expr.var_nm].mat_s.mat_vals->at(2)->at(1), "fmul");

    tmpDet1 = Builder.CreateFAdd(tmpDet2, tmpDet3, "fadd");
    tmpDet1 = Builder.CreateFAdd(tmpDet1, tmpDet4, "fadd");

    tmpDet1 = Builder.CreateFSub(tmpDet1, tmpDet5, "fsub");
    tmpDet1 = Builder.CreateFSub(tmpDet1, tmpDet6, "fsub");
    tmpDet1 = Builder.CreateFSub(tmpDet1, tmpDet7, "fsub");

    vim_tmp.var_val = tmpDet1;

  }else{
    //TODO: support det of matrices > 3x3 ???
    yyerror("ERROR - Can't support DETERMINANT Matrices > 3X3");
    exit(EXIT_FAILURE);
  }

  return vim_tmp;
}

var_imm_mat internal_det_of_3x3(var_imm_mat vim_expr){
  if(vim_expr.is_scalar || !vim_expr.is_var){
    yyerror("ERROR - Can't Transpose non Matrix");
    exit(EXIT_FAILURE);
  }
  if(matVars[vim_expr.var_nm].mat_s.dimens.rowSize != 3){
    yyerror("ERROR - Matrix Must be 3x3");
    exit(EXIT_FAILURE);
  }
  if(matVars[vim_expr.var_nm].mat_s.dimens.rowSize != matVars[vim_expr.var_nm].mat_s.dimens.colSize){
    yyerror("ERROR - Mat Must be Square)");
    exit(EXIT_FAILURE);
  }

  var_imm_mat vim_tmp;
  vim_tmp.is_scalar = false;
  vim_tmp.is_var = true;
  vim_tmp.mat_s.dimens.rowSize = vim_expr.mat_s.dimens.rowSize;
  vim_tmp.mat_s.dimens.colSize = vim_expr.mat_s.dimens.colSize;
  vector<vector<Value*>*> *mat_rows_expr_tmp = new vector<vector<Value*>*>;
  vector<Value*> *mat_cols_expr_tmp;

  var_imm_mat vim_tmp2x2;
  vim_tmp2x2.is_scalar = false;
  vim_tmp2x2.is_var = true;
  vim_tmp2x2.mat_s.dimens.rowSize = 2;
  vim_tmp2x2.mat_s.dimens.colSize = 2;
  vector<vector<Value*>*> *mat_rows;
  vector<Value*> *mat_cols;

  Value* tmpVal0 = ConstantFP::get(Builder.getFloatTy(), (float) 0.0);

  for(int i=0; i<3; i++){
    mat_cols_expr_tmp = new vector<Value*>;
    for(int j=0; j<3; j++){
      mat_rows = new vector<vector<Value*>*>;
      for(int k=0; k<3; k++){
        if(k==i) continue;
        mat_cols = new vector<Value*>;
        for(int l=0; l<3; l++){
          if(l==j) continue;
          mat_cols->push_back(Builder.CreateFAdd(matVars[vim_expr.var_nm].mat_s.mat_vals->at(k)->at(l), tmpVal0, "fadd"));
        }
        mat_rows->push_back(mat_cols);
      }
      vim_tmp2x2.mat_s.mat_vals = mat_rows;
      char *tmpStr =(char*) "__in_place_ido3_0";
      vim_tmp2x2.var_nm = tmpStr;
      matVars[vim_tmp2x2.var_nm] = vim_tmp2x2;
      var_imm_mat detRetTmp = determinant(vim_tmp2x2);

      mat_cols_expr_tmp->push_back(detRetTmp.var_val);
    }
    mat_rows_expr_tmp->push_back(mat_cols_expr_tmp);
  }

  vim_tmp.mat_s.mat_vals = mat_rows_expr_tmp;

  char *tmpStr =(char*) "__in_place_ido3";
  vim_tmp.var_nm = tmpStr;
  matVars[tmpStr] = vim_tmp;

  return vim_tmp;
}

var_imm_mat mat_invert(var_imm_mat vim_expr){
  if(vim_expr.is_scalar || !vim_expr.is_var){
    yyerror("ERROR - Can't Invert non Matrix");
    exit(EXIT_FAILURE);
  }
  if(matVars[vim_expr.var_nm].mat_s.dimens.rowSize != matVars[vim_expr.var_nm].mat_s.dimens.colSize){
    yyerror("ERROR - Mat cannot be inverted (MAT not square)");
    exit(EXIT_FAILURE);
  }

  var_imm_mat detTmp = determinant(vim_expr);
  //TODO: verify that A*A^-1 = A^-1*A = I (indentity matrix) ???
  //  if(detTmp.var_val->isZero()){
  //    yyerror("ERROR - Mat has no Inverse (Determinant is 0)");
  //    exit(EXIT_FAILURE);
  //  }

  var_imm_mat vim_tmp;

  Value* valTmp1 = ConstantFP::get(Builder.getFloatTy(), (float) 1.0);

  var_imm_mat invTmp1;
  invTmp1.is_scalar = true;
  invTmp1.is_var = false;
  invTmp1.var_val = Builder.CreateFDiv(valTmp1, detTmp.var_val, "fdiv");

  if(matVars[vim_expr.var_nm].mat_s.dimens.rowSize == 2){

    var_imm_mat preInvMat;
    preInvMat.is_scalar = false;
    preInvMat.is_var = true;
    preInvMat.mat_s.dimens.rowSize = matVars[vim_expr.var_nm].mat_s.dimens.rowSize;
    preInvMat.mat_s.dimens.colSize = matVars[vim_expr.var_nm].mat_s.dimens.colSize;

    vector<vector<Value*>*> *mat_rows = new vector<vector<Value*>*>;
    vector<Value*> *mat_cols = new vector<Value*>;

    Value* valTmp2, *valTmp3; 

    valTmp2 = ConstantFP::get(Builder.getFloatTy(), (float) 0.0);
    valTmp3 = Builder.CreateFAdd(valTmp2, matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(1), "fadd");
    mat_cols->push_back(valTmp3);
    valTmp3 = Builder.CreateFNeg(matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(1), "fneg");
    mat_cols->push_back(valTmp3);
    mat_rows->push_back(mat_cols);
    mat_cols = new vector<Value*>;
    valTmp3 = Builder.CreateFNeg(matVars[vim_expr.var_nm].mat_s.mat_vals->at(1)->at(0), "fneg");
    mat_cols->push_back(valTmp3);
    valTmp3 = Builder.CreateFAdd(valTmp2, matVars[vim_expr.var_nm].mat_s.mat_vals->at(0)->at(0), "fadd");
    mat_cols->push_back(valTmp3);
    mat_rows->push_back(mat_cols);

    preInvMat.mat_s.mat_vals = mat_rows;

    vim_tmp = expr_expr_mul(invTmp1, preInvMat);
  
  } else if(matVars[vim_expr.var_nm].mat_s.dimens.rowSize == 3){

    var_imm_mat intDet3x3Tmp;
    intDet3x3Tmp = internal_det_of_3x3(vim_expr);

    vim_tmp = expr_expr_div(intDet3x3Tmp, detTmp);

  }else{
    yyerror("ERROR - MAT INVERT - Can't Support > than 3x3 yet");
    exit(EXIT_FAILURE);
  }
  
  char *tmpStr =(char*) "__in_place_mat_invert";
  vim_tmp.var_nm = tmpStr;              
  matVars[tmpStr] = vim_tmp;

  return vim_tmp;
}

var_imm_mat mat_transpose(var_imm_mat vim_expr){
  if(vim_expr.is_scalar || !vim_expr.is_var){
    yyerror("ERROR - Can't Transpose non Matrix");
    exit(EXIT_FAILURE);
  }

  var_imm_mat vim_tmp;

  vim_tmp.is_scalar = false;
  vim_tmp.is_var = true;
  vim_tmp.mat_s.dimens.rowSize = matVars[vim_expr.var_nm].mat_s.dimens.colSize;
  vim_tmp.mat_s.dimens.colSize = matVars[vim_expr.var_nm].mat_s.dimens.rowSize;

  vector<vector<Value*>*> *mat_rows = new vector<vector<Value*>*>;
  vector<Value*> *mat_cols;

  Value* tmpVal0 = ConstantFP::get(Builder.getFloatTy(), (float) 0.0);

  for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
    mat_cols = new vector<Value*>;
    for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
      mat_cols->push_back(Builder.CreateFAdd(vim_expr.mat_s.mat_vals->at(j)->at(i), tmpVal0, "fadd"));
    }
    mat_rows->push_back(mat_cols);
  }

  vim_tmp.mat_s.mat_vals = mat_rows;

  char *tmpStr =(char*) "__in_place_mat_transpose";
  vim_tmp.var_nm = tmpStr;
  matVars[tmpStr] = vim_tmp;

  return vim_tmp;
}

var_imm_mat mat_reduce(var_imm_mat vim_expr){
  if(vim_expr.is_scalar || !vim_expr.is_var){
    yyerror("ERROR - Can't get Reduction of a non Matrix");
    exit(EXIT_FAILURE);
  }

  var_imm_mat vim_tmp;
  vim_tmp.is_scalar = true;
  vim_tmp.is_var = false;
  vim_tmp.var_val = ConstantFP::get(Builder.getFloatTy(), (float) 0.0);

  for(int i=0; i<vim_expr.mat_s.dimens.rowSize; i++){
    for(int j=0; j<vim_expr.mat_s.dimens.colSize; j++){
      vim_tmp.var_val = Builder.CreateFAdd(vim_expr.mat_s.mat_vals->at(i)->at(j), vim_tmp.var_val, "fadd");
    }
  }

  return vim_tmp;
}

var_imm_mat expr_expr_mul(var_imm_mat expr_mat1, var_imm_mat expr_mat2){
  var_imm_mat vim_tmp;

  if(expr_mat1.is_scalar){
    if(expr_mat2.is_scalar){           //************** scalar * scalar ******************

      if(expr_mat1.is_var){
        if(expr_mat2.is_var){
          vim_tmp.is_var = false;
          vim_tmp.is_scalar = true;
          vim_tmp.var_val = Builder.CreateFMul(scalarVars[expr_mat1.var_nm].var_val, scalarVars[expr_mat2.var_nm].var_val, "fmul");
        }else{ 
          vim_tmp.is_var = false;
          vim_tmp.is_scalar = true;
          vim_tmp.var_val = Builder.CreateFMul(scalarVars[expr_mat1.var_nm].var_val, expr_mat2.var_val, "fmul");
        }
      }else{
        if(expr_mat2.is_var){
          vim_tmp.is_var = false;
          vim_tmp.is_scalar = true;
          vim_tmp.var_val = Builder.CreateFMul(expr_mat1.var_val, scalarVars[expr_mat2.var_nm].var_val , "fmul");
        }else{
          vim_tmp.is_var = false;
          vim_tmp.is_scalar = true;
          vim_tmp.var_val = Builder.CreateFMul(expr_mat1.var_val, expr_mat2.var_val, "fmul");
        }
      }
    } else{                //**************** scalar * matrix **********************

      vector<vector<Value*>*> *mat_rows = new vector<vector<Value*>*>;
      vector<Value*> *mat_cols;

      if(expr_mat1.is_var){      // scalar_var  * matrix
        vim_tmp.is_scalar = false;
        vim_tmp.is_var = true;
        vim_tmp.mat_s.dimens.rowSize = matVars[expr_mat2.var_nm].mat_s.dimens.rowSize;
        vim_tmp.mat_s.dimens.colSize = matVars[expr_mat2.var_nm].mat_s.dimens.colSize;

        for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
          mat_cols = new vector<Value*>;
          for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
            mat_cols->push_back(Builder.CreateFMul(scalarVars[expr_mat1.var_nm].var_val, matVars[expr_mat2.var_nm].mat_s.mat_vals->at(i)->at(j), "fmul"));
          }
          mat_rows->push_back(mat_cols);
        }
      }else{            // scalar_literal * mat 

        vim_tmp.is_scalar = false;
        vim_tmp.is_var = true;
        vim_tmp.mat_s.dimens.rowSize = matVars[expr_mat2.var_nm].mat_s.dimens.rowSize;
        vim_tmp.mat_s.dimens.colSize = matVars[expr_mat2.var_nm].mat_s.dimens.colSize;

        for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
          mat_cols = new vector<Value*>;
          for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
            mat_cols->push_back(Builder.CreateFMul(expr_mat1.var_val, matVars[expr_mat2.var_nm].mat_s.mat_vals->at(i)->at(j), "fmul"));
          }
          mat_rows->push_back(mat_cols);
        }
      }
      vim_tmp.mat_s.mat_vals = mat_rows;
    }

  }else{              
    if(!expr_mat2.is_scalar){   //******************* mat * mat ******************  

      vim_tmp = mat_mat_mul(expr_mat1, expr_mat2);

    }else{                      // mat * scalar
      vector<vector<Value*>*> *mat_rows = new vector<vector<Value*>*>;
      vector<Value*> *mat_cols;

      if(expr_mat2.is_var){            // matrix * scalar_var  

        vim_tmp.is_scalar = false;
        vim_tmp.is_var = true;
        vim_tmp.mat_s.dimens.rowSize = matVars[expr_mat1.var_nm].mat_s.dimens.rowSize;
        vim_tmp.mat_s.dimens.colSize = matVars[expr_mat1.var_nm].mat_s.dimens.colSize;

        for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
          mat_cols = new vector<Value*>;
          for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
            mat_cols->push_back(Builder.CreateFMul(scalarVars[expr_mat2.var_nm].var_val, matVars[expr_mat1.var_nm].mat_s.mat_vals->at(i)->at(j), "fmul"));
          }
          mat_rows->push_back(mat_cols);
        }
      }else{            //  mt * scalar_literal 

        vim_tmp.is_scalar = false;
        vim_tmp.is_var = true;
        vim_tmp.mat_s.dimens.rowSize = matVars[expr_mat1.var_nm].mat_s.dimens.rowSize;
        vim_tmp.mat_s.dimens.colSize = matVars[expr_mat1.var_nm].mat_s.dimens.colSize;

        for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
          mat_cols = new vector<Value*>;
          for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
            mat_cols->push_back(Builder.CreateFMul(expr_mat2.var_val, matVars[expr_mat1.var_nm].mat_s.mat_vals->at(i)->at(j), "fmul"));
          }
          mat_rows->push_back(mat_cols);
        }
      }
      vim_tmp.mat_s.mat_vals = mat_rows;
    }
  }

  char *tmpStr =(char*) "__in_place_expr_expr_mul";
  vim_tmp.var_nm = tmpStr;
  matVars[tmpStr] = vim_tmp;

  return vim_tmp;
}

var_imm_mat mat_mat_mul(var_imm_mat vim_mat1, var_imm_mat vim_mat2){
  if(matVars[vim_mat1.var_nm].mat_s.dimens.colSize != matVars[vim_mat2.var_nm].mat_s.dimens.rowSize){
    yyerror("ERROR - Mat Mul with Incompatible Matrices");
    exit(EXIT_FAILURE);
  }

  Value* tmpMul;
  var_imm_mat vim_tmp;
  vector<vector<Value*>*> *mat_rows = new vector<vector<Value*>*>;
  vector<Value*> *mat_cols;

  vim_tmp.is_scalar = false;
  vim_tmp.is_var = true;
  vim_tmp.mat_s.dimens.rowSize = matVars[vim_mat1.var_nm].mat_s.dimens.rowSize;
  vim_tmp.mat_s.dimens.colSize = matVars[vim_mat2.var_nm].mat_s.dimens.colSize;

  //initializing tmpMat to zeros
  Value* tmpVal0 = ConstantFP::get(Builder.getFloatTy(), (float) 0.0);
  for(int i=0; i<matVars[vim_mat1.var_nm].mat_s.dimens.rowSize; i++){
    mat_cols = new vector<Value*>;
    for(int j=0; j<matVars[vim_mat2.var_nm].mat_s.dimens.colSize; j++){
      mat_cols->push_back(tmpVal0);
    }
    mat_rows->push_back(mat_cols);
  }
      
  for(int i=0; i<matVars[vim_mat1.var_nm].mat_s.dimens.rowSize; i++){
    for(int j=0; j<matVars[vim_mat2.var_nm].mat_s.dimens.colSize; j++){
      for(int k=0; k<matVars[vim_mat2.var_nm].mat_s.dimens.rowSize; k++){
        tmpMul = Builder.CreateFMul(matVars[vim_mat1.var_nm].mat_s.mat_vals->at(i)->at(k), matVars[vim_mat2.var_nm].mat_s.mat_vals->at(k)->at(j), "fmul");

        mat_rows->at(i)->at(j) = Builder.CreateFAdd(tmpMul, mat_rows->at(i)->at(j), "fadd");
      }
    }
  }

  vim_tmp.mat_s.mat_vals = mat_rows;

  char *tmpStr =(char*) "__in_place_mat_mat__mul";
  vim_tmp.var_nm = tmpStr;
  matVars[tmpStr] = vim_tmp;

  return vim_tmp;
}

var_imm_mat expr_expr_div(var_imm_mat vim_expr1, var_imm_mat vim_expr3){

  var_imm_mat vim_tmp;

  if(vim_expr1.is_scalar){
    if(!vim_expr3.is_scalar){
      yyerror("Cannot div Scalar with Matrix 1");
      exit(EXIT_FAILURE);
    }

    if(vim_expr1.is_var){
      if(vim_expr3.is_var){
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFDiv(scalarVars[vim_expr1.var_nm].var_val, scalarVars[vim_expr3.var_nm].var_val, "fdiv");
      }else{ 
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFDiv(scalarVars[vim_expr1.var_nm].var_val, vim_expr3.var_val, "fdiv");
      }
    }else{
      if(vim_expr3.is_var){
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFDiv(vim_expr1.var_val, scalarVars[vim_expr3.var_nm].var_val , "fdiv");
      }else{
        vim_tmp.is_var = false;
        vim_tmp.is_scalar = true;
        vim_tmp.var_val = Builder.CreateFDiv(vim_expr1.var_val, vim_expr3.var_val, "fdiv");
      }
    }

  }else{                        // mat Div scalar 
    if(vim_expr3.is_scalar){
      vim_tmp.is_scalar = false;
      vim_tmp.is_var = true;
      vim_tmp.mat_s.dimens.rowSize = vim_expr1.mat_s.dimens.rowSize;
      vim_tmp.mat_s.dimens.colSize = vim_expr1.mat_s.dimens.colSize;
      vector<vector<Value*>*> *mat_rows = new vector<vector<Value*>*>;
      vector<Value*> *mat_cols;

      if(vim_expr3.is_var){            // matrix / scalar_var  

        for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
          mat_cols = new vector<Value*>;
          for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
            mat_cols->push_back(Builder.CreateFDiv(matVars[vim_expr1.var_nm].mat_s.mat_vals->at(i)->at(j), scalarVars[vim_expr3.var_nm].var_val, "fdiv"));
          }
          mat_rows->push_back(mat_cols);
        }
      }else{                  //  mat / scalar_literal 
        for(int i=0; i<vim_tmp.mat_s.dimens.rowSize; i++){
          mat_cols = new vector<Value*>;
          for(int j=0; j<vim_tmp.mat_s.dimens.colSize; j++){
            mat_cols->push_back(Builder.CreateFDiv(matVars[vim_expr1.var_nm].mat_s.mat_vals->at(i)->at(j), vim_expr3.var_val, "fdiv"));
          }
          mat_rows->push_back(mat_cols);
        }
      }
      vim_tmp.mat_s.mat_vals = mat_rows;
    }else{                    // mat Div mat 
      vim_tmp = mat_mat_div(vim_expr1, vim_expr3);
    }
  }

  char *tmpStr =(char*) "__in_place_expr_expr_div";  
  vim_tmp.var_nm = tmpStr;
  matVars[tmpStr] = vim_tmp;

  return vim_tmp;
}

var_imm_mat mat_mat_div(var_imm_mat vim_mat1, var_imm_mat vim_mat2){

  var_imm_mat vim_tmp;

  vim_tmp = mat_invert(vim_mat2);
  vim_tmp = mat_mat_mul(vim_mat1, vim_tmp);

  char *tmpStr =(char*) "__in_place_mat_mat_div";       
  vim_tmp.var_nm = tmpStr;
  matVars[tmpStr] = vim_tmp;

  return vim_tmp;
}

unique_ptr<Module> parseP1File(const string &InputFilename)
{
  string modName = InputFilename;
  if (modName.find_last_of('/') != string::npos)
    modName = modName.substr(modName.find_last_of('/')+1);
  if (modName.find_last_of('.') != string::npos)
    modName.resize(modName.find_last_of('.'));

  // unique_ptr will clean up after us, call destructor, etc.
  unique_ptr<Module> Mptr(new Module(modName.c_str(), TheContext));

  // set global module
  M = Mptr.get();
  
  /* this is the name of the file to generate, you can also use
     this string to figure out the name of the generated function */

  if (InputFilename == "--")
    yyin = stdin;
  else	  
    yyin = fopen(InputFilename.c_str(),"r");

  //yydebug = 1;
  if (yyparse() != 0) {
    // Dump LLVM IR to the screen for debugging
    M->print(errs(),nullptr,false,true);
    // errors, so discard module
    Mptr.reset();
  } else {
    // Dump LLVM IR to the screen for debugging
    M->print(errs(),nullptr,false,true);
  }
  
  return Mptr;
}

void yyerror(const char* msg)
{
  printf("%s\n",msg);
}
