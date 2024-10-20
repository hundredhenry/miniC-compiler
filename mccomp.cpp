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
// Helper functions
//===----------------------------------------------------------------------===//

static bool contains(std::vector<TOKEN_TYPE> vec, int tok) {
  if (std::find(vec.begin(), vec.end(), tok) != vec.end()) {
    return true;
  } else {
    return false;
  }
}

static bool match(int tok) {
  if (CurTok.type == tok) {
    getNextToken();
    return true;
  } else {
    return false;
  }
}

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

//===----------------------------- -----------------------------------------===//
// First and Follow sets for each production rule
//===----------------------------------------------------------------------===//

// First sets of each production
std::vector<TOKEN_TYPE> first_extern_list = {EXTERN};
std::vector<TOKEN_TYPE> first_extern_listP = {EXTERN};
std::vector<TOKEN_TYPE> first_extern = {EXTERN};
std::vector<TOKEN_TYPE> first_decl_list = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
std::vector<TOKEN_TYPE> first_decl_listP = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
std::vector<TOKEN_TYPE> first_decl = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
std::vector<TOKEN_TYPE> first_type_spec = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
std::vector<TOKEN_TYPE> first_var_type = {BOOL_TOK, FLOAT_TOK, INT_TOK};
std::vector<TOKEN_TYPE> first_params = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
std::vector<TOKEN_TYPE> first_param_list = {BOOL_TOK, FLOAT_TOK, INT_TOK};
std::vector<TOKEN_TYPE> first_param_listP = {COMMA};
std::vector<TOKEN_TYPE> first_param = {BOOL_TOK, FLOAT_TOK, INT_TOK};
std::vector<TOKEN_TYPE> first_block = {LBRA};
std::vector<TOKEN_TYPE> first_local_decls = {BOOL_TOK, FLOAT_TOK, INT_TOK};
std::vector<TOKEN_TYPE> first_local_declsP = {BOOL_TOK, FLOAT_TOK, INT_TOK};
std::vector<TOKEN_TYPE> first_local_decl = {BOOL_TOK, FLOAT_TOK, INT_TOK};
std::vector<TOKEN_TYPE> first_stmt_list = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_stmt_listP = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_stmt = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_expr_stmt = {NOT, LPAR, MINUS, SC, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_while_stmt = {WHILE};
std::vector<TOKEN_TYPE> first_if_stmt = {IF};
std::vector<TOKEN_TYPE> first_else_stmt = {ELSE};
std::vector<TOKEN_TYPE> first_return_stmt = {RETURN};
std::vector<TOKEN_TYPE> first_expr = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_logical_or = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_logical_orP = {OR};
std::vector<TOKEN_TYPE> first_logical_and = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_logical_andP = {AND};
std::vector<TOKEN_TYPE> first_equality = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_equalityP = {EQ, NE};
std::vector<TOKEN_TYPE> first_relational = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_relationalP = {LT, LE, GT, GE};
std::vector<TOKEN_TYPE> first_additive = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_additiveP = {PLUS, MINUS};
std::vector<TOKEN_TYPE> first_multiplicative = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_multiplicativeP = {MOD, ASTERIX, DIV};
std::vector<TOKEN_TYPE> first_factor = {LPAR, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_reference = {BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_referenceP = {LPAR};
std::vector<TOKEN_TYPE> first_literal = {BOOL_LIT, FLOAT_LIT, INT_LIT};
std::vector<TOKEN_TYPE> first_args = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_arg_list = {NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> first_arg_listP = {COMMA};

// Follow sets of each production
std::vector<TOKEN_TYPE> follow_extern_listP = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
std::vector<TOKEN_TYPE> follow_decl_listP = {EOF_TOK};
std::vector<TOKEN_TYPE> follow_decl = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK, EOF_TOK};
std::vector<TOKEN_TYPE> follow_params = {RPAR};
std::vector<TOKEN_TYPE> follow_param_listP = {RPAR};
std::vector<TOKEN_TYPE> follow_local_decls = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> follow_local_declsP = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> follow_stmt_list = {RBRA};
std::vector<TOKEN_TYPE> follow_stmt_listP = {RBRA};
std::vector<TOKEN_TYPE> follow_expr_stmt = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> follow_else_stmt = {NOT, LPAR, MINUS, SC, IF, RETURN, WHILE, LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
std::vector<TOKEN_TYPE> follow_expr = {RPAR, COMMA, SC};
std::vector<TOKEN_TYPE> follow_logical_or = {RPAR, COMMA, SC};
std::vector<TOKEN_TYPE> follow_logical_orP = {RPAR, COMMA, SC};
std::vector<TOKEN_TYPE> follow_logical_andP = {RPAR, COMMA, SC, OR};
std::vector<TOKEN_TYPE> follow_equalityP = {AND, RPAR, COMMA, SC, OR};
std::vector<TOKEN_TYPE> follow_relationalP = {NE, AND, RPAR, COMMA, SC, EQ, OR};
std::vector<TOKEN_TYPE> follow_additiveP = {NE, AND, RPAR, COMMA, SC, LT, LE, EQ, GT, GE, OR};
std::vector<TOKEN_TYPE> follow_multiplicativeP = {NE, AND, RPAR, PLUS, MINUS, SC, LT, LE, EQ, GT, GE, OR};
std::vector<TOKEN_TYPE> follow_referenceP = {NE, MOD, AND, RPAR, ASTERIX, PLUS, COMMA, MINUS, DIV, SC, LT, LE, EQ, GT, GE, OR};
std::vector<TOKEN_TYPE> follow_args = {RPAR};
std::vector<TOKEN_TYPE> follow_arg_listP = {RPAR};

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

// Define functions for each production
bool p_extern_list(); bool p_extern_listP();
bool p_extern();
bool p_decl_list(); bool p_decl_listP();
bool p_decl();
bool p_type_spec();
bool p_var_type();
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
bool p_return_stmt();
bool p_expr();
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

// arg_list' -> "," expr arg_list' | ϵ
bool p_arg_listP() {
  if (match(COMMA)) {
    return p_expr() && p_arg_listP();
  } else if (contains(follow_arg_listP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// arg_list -> expr arg_list'
bool p_arg_list() {
  return p_expr() && p_arg_listP();
}

// args -> arg_list | ϵ
bool p_args() {
  if (contains(first_args, CurTok.type)) {
    return p_arg_list();
  } else if (contains(follow_args, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// literal -> INT_LIT | FLOAT_LIT | BOOL_LIT
bool p_literal() {
  if (match(INT_LIT) || match(FLOAT_LIT) || match(BOOL_LIT)) {
    return true;
  } else {
    return false;
  }
}

// reference' -> "(" args ")" | ϵ
bool p_referenceP() {
  if (match(LPAR)) {
    return p_args() && match(RPAR);
  } else if (contains(follow_referenceP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// reference -> IDENT reference' | literal
bool p_reference() {
  if (match(IDENT)) {
    return p_referenceP();
  } else if (contains(first_literal, CurTok.type)) {
    return p_literal();
  } else {
    return false;
  }
}

// factor -> "(" expr ")" | reference
bool p_factor() {
  if (match(LPAR)) {
    return p_expr() && match(RPAR);
  } else if (contains(first_reference, CurTok.type)) {
    return p_reference();
  } else {
    return false;
  }
}

// unary -> "-" unary | "!" unary | factor
bool p_unary() {
  if (match(MINUS) || match(NOT)) {
    return p_unary();
  } else if (contains(first_factor, CurTok.type)) {
    return p_factor();
  } else {
    return false;
  }
}

// multiplicative' -> "*" unary multiplicative' | "/" unary multiplicative' | "%" unary multiplicative' | ϵ
bool p_multiplicativeP() {
  if (match(ASTERIX) || match(DIV) || match(MOD)) {
    return p_unary() && p_multiplicativeP();
  } else if (contains(follow_multiplicativeP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// multiplicative -> unary multiplicative'
bool p_multiplicative() {
  return p_unary() && p_multiplicativeP();
}

// additive' -> "+" multiplicative additive' | "-" multiplicative additive' | ϵ
bool p_additiveP() {
  if (match(PLUS) || match(MINUS)) {
    return p_multiplicative() && p_additiveP();
  } else if (contains(follow_additiveP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// additive -> multiplicative additive'
bool p_additive() {
  return p_multiplicative() && p_additiveP();
}

// relational' -> "<=" additive relational' | "<" additive relational' | ">=" additive relational' | ">" additive relational' | ϵ
bool p_relationalP() {

  if (match(LE) || match(LT) || match(GE) || match(GT)) {
    return p_additive() && p_relationalP();
  } else if (contains(follow_relationalP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// relational -> additive relational'
bool p_relational() {
  return p_additive() && p_relationalP();
}

// equality' -> "==" relational equality' | "!=" relational equality' | ϵ
bool p_equalityP() {
  if (match(EQ) || match(NE)) {
    return p_relational() && p_equalityP();
  } else if (contains(follow_equalityP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// equality -> relational equality'
bool p_equality() {
  return p_relational() && p_equalityP();
}

// logical_and' -> "&&" equality logical_and' | ϵ
bool p_logical_andP() {
  if (match(AND)) {
    return p_equality() && p_logical_andP();
  } else if (contains(follow_logical_andP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// logical_and -> equality logical_and'
bool p_logical_and() {
  return p_equality() && p_logical_andP();
}

// logical_or' -> "||" logical_and logical_or' | ϵ
bool p_logical_orP() {
  if (match(OR)) {
    return p_logical_and() && p_logical_orP();
  } else if (contains(follow_logical_orP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// logical_or -> logical_and logical_or'
bool p_logical_or() {
  return p_logical_and() && p_logical_orP();
}

// expr -> IDENT "=" expr | logical_or
bool p_expr() {
  TOKEN temp = CurTok;
  getNextToken();

  if (temp.type == IDENT && match(ASSIGN)) {
    return p_expr();
  } else if (contains(first_logical_or, temp.type)) {
    putBackToken(CurTok);
    CurTok = temp;
    return p_logical_or();
  } else {
    return false;
  }
}

// return_stmt -> "return" expr_stmt
bool p_return_stmt() {
  return match(RETURN) && p_expr_stmt();
}

// else_stmt -> "else" block | ϵ
bool p_else_stmt() {
  if (match(ELSE)) {
    return p_block();
  } else if (contains(follow_else_stmt, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// if_stmt -> "if" "(" expr ")" stmt else_stmt
bool p_if_stmt() {
  return match(IF) && match(LPAR) && p_expr() && match(RPAR) && p_block() && p_else_stmt();
}

// while_stmt -> "while" "(" expr ")" stmt
bool p_while_stmt() {
  return match(WHILE) && match(LPAR) && p_expr() && match(RPAR) && p_stmt();
}

// expr_stmt -> expr ";" | ";"
bool p_expr_stmt() {
  if (contains(first_expr, CurTok.type)) {
    return p_expr() && match(SC);
  } else if (match(SC)) {
    return true;
  } else {
    return false;
  }
}

// stmt -> expr_stmt | block | if_stmt | while_stmt | return_stmt
bool p_stmt() {
  if (contains(first_expr_stmt, CurTok.type)) {
    return p_expr_stmt();
  } else if (contains(first_block, CurTok.type)) {
    return p_block();
  } else if (contains(first_if_stmt, CurTok.type)) {
    return p_if_stmt();
  } else if (contains(first_while_stmt, CurTok.type)) {
    return p_while_stmt();
  } else if (contains(first_return_stmt, CurTok.type)) {
    return p_return_stmt();
  } else {
    return false;
  }
}

// stmt_list' -> stmt stmt_list' | ϵ
bool p_stmt_listP() {
  if (contains(first_stmt, CurTok.type)) {
    return p_stmt() && p_stmt_listP();
  } else if (contains(follow_stmt_listP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// stmt_list -> stmt stmt_list'
bool p_stmt_list() {
  return p_stmt() && p_stmt_listP();
}

// local_decl -> var_type IDENT ";"
bool p_local_decl() {
  return p_var_type() && match(IDENT) && match(SC);
}

// local_decls' -> local_decl local_decls' | ϵ
bool p_local_declsP() {
  if (contains(first_local_decl, CurTok.type)) {
    return p_local_decl() && p_local_declsP();
  } else if (contains(follow_local_declsP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// local_decls -> local_decls'
bool p_local_decls() {
  return p_local_declsP();
}

// block -> "{" local_decls stmt_list "}"
bool p_block() {
  return match(LBRA) && p_local_decls() && p_stmt_list() && match(RBRA);
}

// param -> var_type IDENT
bool p_param() {
  return p_var_type() && match(IDENT);
}

// param_list' -> "," param param_list' | ϵ
bool p_param_listP() {
  if (match(COMMA)) {
    return p_param() && p_param_listP();
  } else if (contains(follow_param_listP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// param_list -> param param_list'
bool p_param_list() {
  return p_param() && p_param_listP();
}

// params -> param_list | "void" | ϵ
bool p_params() {
  if (contains(first_param_list, CurTok.type)) {
    return p_param_list();
  } else if (match(VOID_TOK)) {
    return true;
  } else if (contains(follow_params, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// var_type -> "int" | "float" | "bool"
bool p_var_type() {
  if (match(INT_TOK) || match(FLOAT_TOK) || match(BOOL_TOK)) {
    return true;
  } else {
    return false;
  }
}

// type_spec -> var_type | "void"
bool p_type_spec() {
  if (contains(first_var_type, CurTok.type)) {
    return p_var_type();
  } else if (match(VOID_TOK)) {
    return true;
  } else {
    return false;
  }
}

// decl -> var_type IDENT ";" | type_spec IDENT "(" params ")" block
// This is messy
bool p_decl() {
  if (contains(first_var_type, CurTok.type)) { // Will be "int", "float", or "bool"
    if (!p_var_type() || !match(IDENT)) {
      return false;
    }

    if (match(SC)) {
      return true;
    } else if (match(LPAR) && p_params() && match(RPAR) && p_block()) {
      return true;
    } else {
      return false;
    }
  } else if (contains(first_type_spec, CurTok.type)) { // Will only be "void"
    return p_type_spec() && match(IDENT) && match(LPAR) && p_params() && match(RPAR) && p_block();
  } else {
    return false;
  }
}

// decl_list' -> decl decl_list' | ϵ
bool p_decl_listP() {
  if (contains(first_decl, CurTok.type)) {
    return p_decl() && p_decl_listP();
  } else if (contains(follow_decl_listP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// decl_list -> decl decl_list'
bool p_decl_list() {
  return p_decl() && p_decl_listP();
}

// extern -> "extern" type_spec IDENT "(" params ")" ";"
bool p_extern() {
  return match(EXTERN) && p_type_spec() && match(IDENT) && match(LPAR) && p_params() && match(RPAR) && match(SC);
}

// extern_list' -> extern extern_list' | ϵ
bool p_extern_listP() {
  if (contains(first_extern, CurTok.type)) {
    return p_extern() && p_extern_listP();
  } else if (contains(follow_extern_listP, CurTok.type)) {
    return true;
  } else {
    return false;
  }
}

// extern_list -> extern extern_list'
bool p_extern_list() {
  return p_extern() && p_extern_listP();
}

// program -> extern_list decl_list | decl_list
bool p_program() {
  if (contains(first_extern_list, CurTok.type)) {
    return p_extern_list() && p_decl_list();
  } else if (contains(first_decl_list, CurTok.type)) {
    return p_decl_list();
  } else {
    return false;
  }
}

static void parser() {
  getNextToken(); // Consume EOF

  if (p_program() && CurTok.type == EOF_TOK) {
    fprintf(stderr, "Parsing Successful\n");
  } else {
    fprintf(stderr, "Parsing Failed\n");
  }
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
  //getNextToken();
  //while (CurTok.type != EOF_TOK) {
  //  fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
  //          CurTok.type);
  //  getNextToken();
  //}
  //fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = std::make_unique<Module>("mini-c", TheContext);

  // Reset the file pointer to the beginning of the file
  
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
