#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <string.h>
#include <string>
#include <system_error>
#include <utility>
#include <vector>

using namespace llvm;
using namespace llvm::sys;

FILE *pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns one of these for known things.
enum TOKEN_TYPE {

  IDENT = -1,        // [a-zA-Z_][a-zA-Z_0-9]*
  ASSIGN = int('='), // '='

  // delimiters
  LBRA = int('{'),  // left brace
  RBRA = int('}'),  // right brace
  LPAR = int('('),  // left parenthesis
  RPAR = int(')'),  // right parenthesis
  SC = int(';'),    // semicolon
  COMMA = int(','), // comma

  // types
  INT_TOK = -2,   // "int"
  VOID_TOK = -3,  // "void"
  FLOAT_TOK = -4, // "float"
  BOOL_TOK = -5,  // "bool"

  // keywords
  EXTERN = -6,  // "extern"
  IF = -7,      // "if"
  ELSE = -8,    // "else"
  WHILE = -9,   // "while"
  RETURN = -10, // "return"
  // TRUE   = -12,     // "true"
  // FALSE   = -13,     // "false"

  // literals
  INT_LIT = -14,   // [0-9]+
  FLOAT_LIT = -15, // [0-9]+.[0-9]+
  BOOL_LIT = -16,  // "true" or "false" key words

  // logical operators
  AND = -17, // "&&"
  OR = -18,  // "||"

  // operators
  PLUS = int('+'),    // addition or unary plus
  MINUS = int('-'),   // substraction or unary negative
  ASTERIX = int('*'), // multiplication
  DIV = int('/'),     // division
  MOD = int('%'),     // modular
  NOT = int('!'),     // unary negation

  // comparison operators
  EQ = -19,      // equal
  NE = -20,      // not equal
  LE = -21,      // less than or equal to
  LT = int('<'), // less than
  GE = -23,      // greater than or equal to
  GT = int('>'), // greater than

  // special tokens
  EOF_TOK = 0, // signal end of file

  // invalid
  INVALID = -100 // signal invalid token
};

// TOKEN struct is used to keep track of information about a token
struct TOKEN {
  int type = -100;
  std::string lexeme;
  int lineNo;
  int columnNo;
};

static std::string IdentifierStr; // Filled in if IDENT
static int IntVal;                // Filled in if INT_LIT
static bool BoolVal;              // Filled in if BOOL_LIT
static float FloatVal;            // Filled in if FLOAT_LIT
static std::string StringVal;     // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(std::string lexVal, int tok_type) {
  TOKEN return_tok;
  return_tok.lexeme = lexVal;
  return_tok.type = tok_type;
  return_tok.lineNo = lineNo;
  return_tok.columnNo = columnNo - lexVal.length() - 1;
  return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
/// gettok - Return the next token from standard input.
static TOKEN gettok() {

  static int LastChar = ' ';
  static int NextChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar)) {
    if (LastChar == '\n' || LastChar == '\r') {
      lineNo++;
      columnNo = 1;
    }
    LastChar = getc(pFile);
    columnNo++;
  }

  if (isalpha(LastChar) ||
      (LastChar == '_')) { // identifier: [a-zA-Z_][a-zA-Z_0-9]*
    IdentifierStr = LastChar;
    columnNo++;

    while (isalnum((LastChar = getc(pFile))) || (LastChar == '_')) {
      IdentifierStr += LastChar;
      columnNo++;
    }

    if (IdentifierStr == "int")
      return returnTok("int", INT_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "float")
      return returnTok("float", FLOAT_TOK);
    if (IdentifierStr == "void")
      return returnTok("void", VOID_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "extern")
      return returnTok("extern", EXTERN);
    if (IdentifierStr == "if")
      return returnTok("if", IF);
    if (IdentifierStr == "else")
      return returnTok("else", ELSE);
    if (IdentifierStr == "while")
      return returnTok("while", WHILE);
    if (IdentifierStr == "return")
      return returnTok("return", RETURN);
    if (IdentifierStr == "true") {
      BoolVal = true;
      return returnTok("true", BOOL_LIT);
    }
    if (IdentifierStr == "false") {
      BoolVal = false;
      return returnTok("false", BOOL_LIT);
    }

    return returnTok(IdentifierStr.c_str(), IDENT);
  }

  if (LastChar == '=') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // EQ: ==
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("==", EQ);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("=", ASSIGN);
    }
  }

  if (LastChar == '{') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("{", LBRA);
  }
  if (LastChar == '}') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("}", RBRA);
  }
  if (LastChar == '(') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("(", LPAR);
  }
  if (LastChar == ')') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(")", RPAR);
  }
  if (LastChar == ';') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(";", SC);
  }
  if (LastChar == ',') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(",", COMMA);
  }

  if (isdigit(LastChar) || LastChar == '.') { // Number: [0-9]+.
    std::string NumStr;

    if (LastChar == '.') { // Floating point Number: .[0-9]+
      do {
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      FloatVal = strtof(NumStr.c_str(), nullptr);
      return returnTok(NumStr, FLOAT_LIT);
    } else {
      do { // Start of Number: [0-9]+
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      if (LastChar == '.') { // Floating point Number: [0-9]+.[0-9]+)
        do {
          NumStr += LastChar;
          LastChar = getc(pFile);
          columnNo++;
        } while (isdigit(LastChar));

        FloatVal = strtof(NumStr.c_str(), nullptr);
        return returnTok(NumStr, FLOAT_LIT);
      } else { // Integer : [0-9]+
        IntVal = strtod(NumStr.c_str(), nullptr);
        return returnTok(NumStr, INT_LIT);
      }
    }
  }

  if (LastChar == '&') {
    NextChar = getc(pFile);
    if (NextChar == '&') { // AND: &&
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("&&", AND);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("&", int('&'));
    }
  }

  if (LastChar == '|') {
    NextChar = getc(pFile);
    if (NextChar == '|') { // OR: ||
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("||", OR);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("|", int('|'));
    }
  }

  if (LastChar == '!') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // NE: !=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("!=", NE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("!", NOT);
      ;
    }
  }

  if (LastChar == '<') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // LE: <=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("<=", LE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("<", LT);
    }
  }

  if (LastChar == '>') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // GE: >=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok(">=", GE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok(">", GT);
    }
  }

  if (LastChar == '/') { // Could be division or could be the start of a comment
    LastChar = getc(pFile);
    columnNo++;
    if (LastChar == '/') { // Definitely a comment
      do {
        LastChar = getc(pFile);
        columnNo++;
      } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

      if (LastChar != EOF)
        return gettok();
    } else
      return returnTok("/", DIV);
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF) {
    columnNo++;
    return returnTok("0", EOF_TOK);
  }

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  std::string s(1, ThisChar);
  LastChar = getc(pFile);
  columnNo++;
  return returnTok(s, int(ThisChar));
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;

static TOKEN getNextToken() {

  if (tok_buffer.size() == 0)
    tok_buffer.push_back(gettok());

  TOKEN temp = tok_buffer.front();
  tok_buffer.pop_front();

  return CurTok = temp;
}

static void putBackToken(TOKEN tok) { tok_buffer.push_front(tok); }

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

/// ASTnode - Base class for all AST nodes.
class ASTnode {
public:
  virtual ~ASTnode() {}
  virtual Value *codegen() = 0;
  virtual std::string to_string() const {return "";};
};

/// IntASTnode - Class for integer literals.
class IntASTnode : public ASTnode {
  int Val;
  TOKEN Tok;
  std::string Name;

public:
  IntASTnode(TOKEN tok, int val) : Val(val), Tok(tok) {}
  virtual Value *codegen() override;
  virtual std::string to_string() const override {
    return "IntASTnode: " + std::to_string(Val);
  };
};


//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

/* Add function calls for each production */
bool p_extern_list(); bool p_extern_listP();
bool p_extern();
bool p_decl_list(); bool p_decl_listP();
bool p_decl();
bool p_var_decl();
bool p_type_spec();
bool p_var_type();
bool p_fun_decl();
bool p_params();
bool p_param_list(); bool p_param_listP();
bool p_param();
bool p_block();
bool p_local_decls(); bool p_local_declsP();
bool p_local_decl();
bool p_stmt_list(); bool p_stmt_listP();
bool p_stmt();
bool p_expr_stmt();
bool p_while_stmt();
bool p_if_stmt();
bool p_else_stmt();
bool p_return_stmt(); bool p_return_stmtP();
bool p_expr();
bool p_assignment();
bool p_logical_or(); bool p_logical_orP();
bool p_logical_and(); bool p_logical_andP();
bool p_equality(); bool p_equalityP();
bool p_relational(); bool p_relationalP();
bool p_additive(); bool p_additiveP();
bool p_multiplicative(); bool p_multiplicativeP();
bool p_unary();
bool p_factor();
bool p_reference(); bool p_referenceP();
bool p_literal();
bool p_args();
bool p_arg_list(); bool p_arg_listP();

/* First sets of each production */
TOKEN_TYPE first_extern_list[] = {EXTERN};
TOKEN_TYPE first_decl_list[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
TOKEN_TYPE first_decl_listP[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
TOKEN_TYPE first_decl[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
TOKEN_TYPE first_var_decl[] = {BOOL_TOK, FLOAT_TOK, INT_TOK};
TOKEN_TYPE first_type_spec[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
TOKEN_TYPE first_var_type[] = {BOOL_TOK, FLOAT_TOK, INT_TOK};
TOKEN_TYPE first_fun_decl[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
TOKEN_TYPE first_params[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
TOKEN_TYPE first_param_list[] = {BOOL_TOK, FLOAT_TOK, INT_TOK};
TOKEN_TYPE first_param_listP[] = {COMMA};
TOKEN_TYPE first_param[] = {BOOL_TOK, FLOAT_TOK, INT_TOK};
TOKEN_TYPE first_block[] = {LBRA};
TOKEN_TYPE first_local_decls[] = {BOOL_TOK, FLOAT_TOK, INT_TOK};
TOKEN_TYPE first_local_declsP[] = {BOOL_TOK, FLOAT_TOK, INT_TOK};
TOKEN_TYPE first_local_decl[] = {BOOL_TOK, FLOAT_TOK, INT_TOK};
TOKEN_TYPE first_stmt_list[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_stmt_listP[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_stmt[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_expr_stmt[] = {NOT, LPAR, MINUS, SC, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_while_stmt[] = {WHILE};
TOKEN_TYPE first_if_stmt[] = {IF};
TOKEN_TYPE first_else_stmt[] = {ELSE};
TOKEN_TYPE first_return_stmt[] = {RETURN};
TOKEN_TYPE first_return_stmtP[] = {NOT, LPAR, MINUS, SC, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_expr[] = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_logical_or[] = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_logical_orP[] = {OR};
TOKEN_TYPE first_logical_and[] = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_logical_andP[] = {AND};
TOKEN_TYPE first_equality[] = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_equalityP[] = {EQ, NE};
TOKEN_TYPE first_relational[] = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_relationalP[] = {LT, LE, GT, GE};
TOKEN_TYPE first_additive[] = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_additiveP[] = {PLUS, MINUS};
TOKEN_TYPE first_multiplicative[] = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_multiplicativeP[] = {MOD, ASTERIX, DIV};
TOKEN_TYPE first_factor[] = {LPAR, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_reference[] = {BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_referenceP[] = {LPAR};
TOKEN_TYPE first_literal[] = {BOOL_LIT, FLOAT_LIT, INT_LIT};
TOKEN_TYPE first_args[] = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_arg_list[] = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE first_arg_listP[] = {COMMA};

/* Follow sets of each production */
TOKEN_TYPE follow_extern_list[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
TOKEN_TYPE follow_extern_listP[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
TOKEN_TYPE follow_extern[] = {BOOL_TOK, EXTERN, FLOAT_TOK, INT_TOK, VOID_TOK};
TOKEN_TYPE follow_decl_list[] = {EOF_TOK};
TOKEN_TYPE follow_decl_listP[] = {EOF_TOK};
TOKEN_TYPE follow_decl[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK, EOF_TOK};
TOKEN_TYPE follow_var_decl[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK, EOF_TOK};
TOKEN_TYPE follow_type_spec[] = {IDENT};
TOKEN_TYPE follow_var_type[] = {IDENT};
TOKEN_TYPE follow_fun_decl[] = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK, EOF_TOK};
TOKEN_TYPE follow_params[] = {RPAR};
TOKEN_TYPE follow_param_list[] = {RPAR};
TOKEN_TYPE follow_param_listP[] = {RPAR};
TOKEN_TYPE follow_param[] = {RPAR, COMMA};
TOKEN_TYPE follow_block[] = {NOT, LPAR, MINUS, SC, BOOL_TOK, ELSE, FLOAT_TOK, IF, INT_TOK, RETURN, VOID_TOK, WHILE, LBRA, RBRA, 
                            EOF_TOK, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_local_decls[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_local_declsP[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_local_decl[] = {NOT, LPAR, MINUS, SC, BOOL_TOK, FLOAT_TOK, IF, INT_TOK, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, 
                                 FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_stmt_list[] = {RBRA};
TOKEN_TYPE follow_stmt_listP[] = {RBRA};
TOKEN_TYPE follow_stmt[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_expr_stmt[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_while_stmt[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_if_stmt[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_else_stmt[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_return_stmt[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_return_stmtP[] = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
TOKEN_TYPE follow_expr[] = {RPAR, COMMA, SC};
TOKEN_TYPE follow_logical_or[] = {RPAR, COMMA, SC};
TOKEN_TYPE follow_logical_orP[] = {RPAR, COMMA, SC};
TOKEN_TYPE follow_logical_and[] = {RPAR, COMMA, SC, OR};
TOKEN_TYPE follow_logical_andP[] = {RPAR, COMMA, SC, OR};
TOKEN_TYPE follow_equality[] = {AND, RPAR, COMMA, SC, OR};
TOKEN_TYPE follow_equalityP[] = {AND, RPAR, COMMA, SC, OR};
TOKEN_TYPE follow_relational[] = {NE, AND, RPAR, COMMA, SC, EQ, OR};
TOKEN_TYPE follow_relationalP[] = {NE, AND, RPAR, COMMA, SC, EQ, OR};
TOKEN_TYPE follow_additive[] = {NE, AND, RPAR, COMMA, SC, LT, LE, EQ, GT, GE, OR};
TOKEN_TYPE follow_additiveP[] = {NE, AND, RPAR, COMMA, SC, LT, LE, EQ, GT, GE, OR};
TOKEN_TYPE follow_multiplicative[] = {NE, AND, RPAR, PLUS, MINUS, SC, LT, LE, EQ, GT, GE, OR};
TOKEN_TYPE follow_multiplicativeP[] = {NE, AND, RPAR, PLUS, MINUS, SC, LT, LE, EQ, GT, GE, OR};
TOKEN_TYPE follow_factor[] = {NE, MOD, AND, RPAR, ASTERIX, PLUS, MINUS, DIV, SC, LT, LE, EQ, GT, GE, OR};
TOKEN_TYPE follow_reference[] = {NE, MOD, AND, RPAR, ASTERIX, PLUS, COMMA, MINUS, DIV, SC, LT, LE, EQ, GT, GE, OR};
TOKEN_TYPE follow_referenceP[] = {NE, MOD, AND, RPAR, ASTERIX, PLUS, COMMA, MINUS, DIV, SC, LT, LE, EQ, GT, GE, OR};
TOKEN_TYPE follow_literal[] = {NE, MOD, AND, RPAR, ASTERIX, PLUS, COMMA, MINUS, DIV, SC, LT, LE, EQ, GT, GE, OR};
TOKEN_TYPE follow_args[] = {RPAR};
TOKEN_TYPE follow_arg_list[] = {RPAR};
TOKEN_TYPE follow_arg_listP[] = {RPAR};

// program ::= extern_list decl_list
static void parser() {
  // add body
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const ASTnode &ast) {
  os << ast.to_string();
  return os;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char **argv) {
  if (argc == 2) {
    pFile = fopen(argv[1], "r");
    if (pFile == NULL)
      perror("Error opening file");
  } else {
    std::cout << "Usage: ./code InputFile\n";
    return 1;
  }

  // initialize line number and column numbers to zero
  lineNo = 1;
  columnNo = 1;

  // get the first token
  getNextToken();
  while (CurTok.type != EOF_TOK) {
    fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
            CurTok.type);
    getNextToken();
  }
  fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = std::make_unique<Module>("mini-c", TheContext);

  // Run the parser now.
  parser();
  fprintf(stderr, "Parsing Finished\n");

  //********************* Start printing final IR **************************
  // Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }
  // TheModule->print(errs(), nullptr); // print IR to terminal
  TheModule->print(dest, nullptr);
  //********************* End printing final IR ****************************

  fclose(pFile); // close the file that contains the code that was parsed
  return 0;
}
