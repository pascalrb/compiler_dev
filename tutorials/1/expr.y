%{
#include <cstdio>
#include <list>
#include <iostream>
#include <string>
#include <memory>
#include <stdexcept>

using namespace std;

extern FILE *yyin;         // defined in expr.lex
int yylex();               // defined in expr.lex
void yyerror(const char*); // defined in expr.lex

extern "C" {
  // this function is generated by bison from the rules in this file.
  int yyparse();
}

// helper code for string formatting.
template<typename ... Args>
std::string format( const std::string& format, Args ... args )
{
    size_t size = snprintf( nullptr, 0, format.c_str(), args ... ) + 1; // Extra space for '\0'
    if( size <= 0 ){ throw std::runtime_error( "Error during formatting." ); }
    std::unique_ptr<char[]> buf( new char[ size ] ); 
    snprintf( buf.get(), size, format.c_str(), args ... );
    return std::string( buf.get(), buf.get() + size - 1 ); // We don't want the '\0' inside
}

 
%}

// Make the output verbose
%verbose
%define parse.trace


%token REG
%token IMMEDIATE
%token ASSIGN SEMI PLUS MINUS LPAREN RPAREN LBRACKET RBRACKET

%type  expr

%left  PLUS MINUS

%%

program:   REG ASSIGN expr SEMI
{
  return 0; // if we get here, we succeeded!
}
;

expr: IMMEDIATE
{

}
| REG
{ 

}
| expr PLUS expr
{

}
| expr MINUS expr
{

}
| LPAREN expr RPAREN
{

}
| MINUS expr
{

}
| LBRACKET expr RBRACKET
{

}
;

%%

void yyerror(const char* msg)
{
  printf("%s",msg);
}

int main(int argc, char *argv[])
{
  yydebug = 0;
  yyin = stdin;
  yyparse();
  return 0;
}
