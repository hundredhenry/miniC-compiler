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
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/Host.h"
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
using namespace std;

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
  string lexeme;
  int lineNo;
  int columnNo;
};

static string IdentifierStr; // Filled in if IDENT
static int IntVal;           // Filled in if INT_LIT
static bool BoolVal;         // Filled in if BOOL_LIT
static float FloatVal;       // Filled in if FLOAT_LIT
static string StringVal;     // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(string lexVal, int tok_type) {
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
    string NumStr;

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
  string s(1, ThisChar);
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
static deque<TOKEN> tok_buffer;

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

static bool contains(vector<TOKEN_TYPE> vec, int tok) {
  if (find(vec.begin(), vec.end(), tok) != vec.end()) {
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

/// ASTNode - Base class for all AST nodes.
class ASTNode {
public:
  virtual ~ASTNode() {}
  virtual Value *codegen() = 0;
  virtual string to_string() const { return ""; };
};

/// IntASTNode - Class for integer literals.
class IntASTNode : public ASTNode {
  TOKEN Tok;
  int Val;

public:
  IntASTNode(TOKEN tok, int val) : Tok(tok), Val(val) {}
  virtual Value *codegen() override;
  virtual string to_string() const override {
    return "IntASTNode: " + ::to_string(Val);
  };
};

/// FloatASTNode - Class for float literals.
class FloatASTNode : public ASTNode {
  TOKEN Tok;
  float Val;

public:
  FloatASTNode(TOKEN tok, float val) : Tok(tok), Val(val) {}
  virtual Value *codegen() override;
  virtual string to_string() const override {
    return "FloatASTNode: " + ::to_string(Val);
  };
};

/// BoolASTNode - Class for boolean literals.
class BoolASTNode : public ASTNode {
  TOKEN Tok;
  bool Val;

public:
  BoolASTNode(TOKEN tok, bool val) : Tok(tok), Val(val) {}
  virtual Value *codegen() override;
  virtual string to_string() const override {
    return "BoolASTNode: " + ::to_string(Val);
  };
};

/// VarASTNode - Class for variable declarations.
class VarASTNode : public ASTNode {
  TOKEN Tok;
  int Type;
  string Name;

public:
  VarASTNode(TOKEN tok, int type, const string &name)
      : Tok(tok), Type(type), Name(name) {}
  virtual Value *codegen() override;
  virtual string to_string() const override { return "VarASTNode: " + Name; };
};

/// VarReferenceASTNode - Class for variable references.
class VarReferenceASTNode : public ASTNode {
  TOKEN Tok;
  string Name;

public:
  VarReferenceASTNode(TOKEN tok, const string &name) : Tok(tok), Name(name) {}
  virtual Value *codegen() override;
  virtual string to_string() const override {
    return "VarRefereneASTNode: " + Name;
  };
};

/// UnaryASTNode - Class for unary operators.
class UnaryASTNode : public ASTNode {
  TOKEN Tok;
  int Op;
  unique_ptr<ASTNode> Operand;

public:
  UnaryASTNode(TOKEN tok, int op, unique_ptr<ASTNode> operand)
      : Tok(tok), Op(op), Operand(std::move(operand)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override {
    return "UnaryASTNode: " + ::to_string(Op);
  };
};

/// BinaryASTNode - Class for binary operators.
class BinaryASTNode : public ASTNode {
  TOKEN Tok;
  int Op;
  unique_ptr<ASTNode> LHS, RHS;

public:
  BinaryASTNode(TOKEN tok, int op, unique_ptr<ASTNode> lhs,
                unique_ptr<ASTNode> rhs)
      : Tok(tok), Op(op), LHS(std::move(lhs)), RHS(std::move(rhs)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override {
    return "BinaryASTNode: " + ::to_string(Op);
  };
};

/// CallASTNode - Class for function calls.
class CallASTNode : public ASTNode {
  TOKEN Tok;
  string Func;
  vector<unique_ptr<ASTNode>> Args;

public:
  CallASTNode(TOKEN tok, const string &func, vector<unique_ptr<ASTNode>> args)
      : Tok(tok), Func(func), Args(std::move(args)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override { return "CallASTNode: " + Func; };
};

/// BlockASTNode - Class for blocks.
class BlockASTNode : public ASTNode {
  vector<unique_ptr<VarASTNode>> LocalDecls;
  vector<unique_ptr<ASTNode>> StmtList;

public:
  BlockASTNode(vector<unique_ptr<VarASTNode>> localDecls,
               vector<unique_ptr<ASTNode>> stmtList)
      : LocalDecls(std::move(localDecls)), StmtList(std::move(stmtList)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override { return "BlockASTNode"; };
};

/// IfASTNode - Class for if statements.
class IfASTNode : public ASTNode {
  TOKEN Tok;
  unique_ptr<ASTNode> Cond;
  unique_ptr<BlockASTNode> Then, Else;

public:
  IfASTNode(TOKEN tok, unique_ptr<ASTNode> cond, unique_ptr<BlockASTNode> then,
            unique_ptr<BlockASTNode> els)
      : Tok(tok), Cond(std::move(cond)), Then(std::move(then)),
        Else(std::move(els)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override { return "IfASTNode"; };
};

/// WhileASTNode - Class for while statements.
class WhileASTNode : public ASTNode {
  TOKEN Tok;
  unique_ptr<ASTNode> Cond;
  unique_ptr<ASTNode> Stmt;

public:
  WhileASTNode(TOKEN tok, unique_ptr<ASTNode> cond, unique_ptr<ASTNode> stmt)
      : Tok(tok), Cond(std::move(cond)), Stmt(std::move(stmt)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override { return "WhileASTNode"; };
};

/// ReturnASTNode - Class for return statements.
class ReturnASTNode : public ASTNode {
  TOKEN Tok;
  unique_ptr<ASTNode> Expr;

public:
  ReturnASTNode(TOKEN tok, unique_ptr<ASTNode> expr)
      : Tok(tok), Expr(std::move(expr)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override { return "ReturnASTNode"; };
};

/// ExternASTNode - Class for extern declarations.
class ExternASTNode : public ASTNode {
  string Name;
  vector<unique_ptr<VarASTNode>> Args;

public:
  ExternASTNode(const string &name, vector<unique_ptr<VarASTNode>> args)
      : Name(name), Args(std::move(args)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override {
    return "ExternASTNode: " + Name;
  };
};

/// FunctionASTNode - Class for function definitions.
class FunctionASTNode : public ASTNode {
  int Type;
  string Name;
  vector<unique_ptr<VarASTNode>> Args;
  unique_ptr<BlockASTNode> Body;

public:
  FunctionASTNode(int type, const string &name,
                  vector<unique_ptr<VarASTNode>> args,
                  unique_ptr<BlockASTNode> body)
      : Type(type), Name(name), Args(std::move(args)), Body(std::move(body)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override {
    return "FunctionASTNode: " + Name;
  };
};

/// ProgramASTNode - Class for the top-level program.
class ProgramASTNode : public ASTNode {
  vector<unique_ptr<ExternASTNode>> Externs;
  vector<unique_ptr<ASTNode>> Decls;

public:
  ProgramASTNode(vector<unique_ptr<ExternASTNode>> externs,
                 vector<unique_ptr<ASTNode>> decls)
      : Externs(std::move(externs)), Decls(std::move(decls)) {}
  virtual Value *codegen() override;
  virtual string to_string() const override { return "ProgramASTNode"; };
};

//===-----------------------------
//-----------------------------------------===//
// First and Follow sets for each production rule
//===----------------------------------------------------------------------===//

// First sets of each production
const vector<TOKEN_TYPE> first_extern_list = {EXTERN};
const vector<TOKEN_TYPE> first_extern_listP = {EXTERN};
const vector<TOKEN_TYPE> first_extern = {EXTERN};
const vector<TOKEN_TYPE> first_decl_list = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                            VOID_TOK};
const vector<TOKEN_TYPE> first_decl_listP = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                             VOID_TOK};
const vector<TOKEN_TYPE> first_decl = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
const vector<TOKEN_TYPE> first_type_spec = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                            VOID_TOK};
const vector<TOKEN_TYPE> first_var_type = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_params = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                         VOID_TOK};
const vector<TOKEN_TYPE> first_param_list = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_param_listP = {COMMA};
const vector<TOKEN_TYPE> first_param = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_block = {LBRA};
const vector<TOKEN_TYPE> first_local_decls = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_local_declsP = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_local_decl = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_stmt_list = {
    NOT,   LPAR, MINUS,    SC,        IF,    RETURN,
    WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_stmt_listP = {
    NOT,   LPAR, MINUS,    SC,        IF,    RETURN,
    WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_stmt = {NOT,      LPAR,      MINUS, SC,
                                       IF,       RETURN,    WHILE, LBRA,
                                       BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_expr_stmt = {
    NOT, LPAR, MINUS, SC, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_while_stmt = {WHILE};
const vector<TOKEN_TYPE> first_if_stmt = {IF};
const vector<TOKEN_TYPE> first_else_stmt = {ELSE};
const vector<TOKEN_TYPE> first_return_stmt = {RETURN};
const vector<TOKEN_TYPE> first_expr = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                       FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_logical_or = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                             FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_logical_orP = {OR};
const vector<TOKEN_TYPE> first_logical_and = {
    NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_logical_andP = {AND};
const vector<TOKEN_TYPE> first_equality = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                           FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_equalityP = {EQ, NE};
const vector<TOKEN_TYPE> first_relational = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                             FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_relationalP = {LT, LE, GT, GE};
const vector<TOKEN_TYPE> first_additive = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                           FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_additiveP = {PLUS, MINUS};
const vector<TOKEN_TYPE> first_multiplicative = {
    NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_multiplicativeP = {MOD, ASTERIX, DIV};
const vector<TOKEN_TYPE> first_factor = {LPAR, BOOL_LIT, FLOAT_LIT, IDENT,
                                         INT_LIT};
const vector<TOKEN_TYPE> first_reference = {BOOL_LIT, FLOAT_LIT, IDENT,
                                            INT_LIT};
const vector<TOKEN_TYPE> first_referenceP = {LPAR};
const vector<TOKEN_TYPE> first_literal = {BOOL_LIT, FLOAT_LIT, INT_LIT};
const vector<TOKEN_TYPE> first_args = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                       FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_arg_list = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                           FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_arg_listP = {COMMA};

// Follow sets of each production
const vector<TOKEN_TYPE> follow_extern_listP = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                                VOID_TOK};
const vector<TOKEN_TYPE> follow_decl = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK,
                                        EOF_TOK};
const vector<TOKEN_TYPE> follow_decl_listP = {EOF_TOK};
const vector<TOKEN_TYPE> follow_params = {RPAR};
const vector<TOKEN_TYPE> follow_param_listP = {RPAR};
const vector<TOKEN_TYPE> follow_local_decls = {
    NOT,  LPAR, MINUS,    SC,        IF,    RETURN, WHILE,
    LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> follow_local_declsP = {
    NOT,  LPAR, MINUS,    SC,        IF,    RETURN, WHILE,
    LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> follow_stmt_list = {RBRA};
const vector<TOKEN_TYPE> follow_stmt_listP = {RBRA};
const vector<TOKEN_TYPE> follow_expr_stmt = {
    NOT,  LPAR, MINUS,    SC,        IF,    RETURN, WHILE,
    LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> follow_else_stmt = {
    NOT,  LPAR, MINUS,    SC,        IF,    RETURN, WHILE,
    LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> follow_expr = {RPAR, COMMA, SC};
const vector<TOKEN_TYPE> follow_logical_or = {RPAR, COMMA, SC};
const vector<TOKEN_TYPE> follow_logical_orP = {RPAR, COMMA, SC};
const vector<TOKEN_TYPE> follow_logical_andP = {RPAR, COMMA, SC, OR};
const vector<TOKEN_TYPE> follow_equalityP = {AND, RPAR, COMMA, SC, OR};
const vector<TOKEN_TYPE> follow_relationalP = {NE, AND, RPAR, COMMA,
                                               SC, EQ,  OR};
const vector<TOKEN_TYPE> follow_additiveP = {NE, AND, RPAR, COMMA, SC, LT,
                                             LE, EQ,  GT,   GE,    OR};
const vector<TOKEN_TYPE> follow_multiplicativeP = {
    NE, AND, RPAR, PLUS, MINUS, SC, LT, LE, EQ, GT, GE, OR};
const vector<TOKEN_TYPE> follow_referenceP = {
    NE,  MOD, AND, RPAR, ASTERIX, PLUS, COMMA, MINUS,
    DIV, SC,  LT,  LE,   EQ,      GT,   GE,    OR};
const vector<TOKEN_TYPE> follow_args = {RPAR};
const vector<TOKEN_TYPE> follow_arg_listP = {RPAR};

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

// Function prototypes
vector<unique_ptr<ASTNode>> p_arg_listP(vector<unique_ptr<ASTNode>> &arg_list);
vector<unique_ptr<ASTNode>> p_arg_list();
vector<unique_ptr<ASTNode>> p_args();
unique_ptr<ASTNode> p_literal();
vector<unique_ptr<ASTNode>> p_referenceP();
unique_ptr<ASTNode> p_reference();
unique_ptr<ASTNode> p_factor();
unique_ptr<ASTNode> p_unary();
unique_ptr<ASTNode> p_multiplicativeP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_multiplicative();
unique_ptr<ASTNode> p_additiveP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_additive();
unique_ptr<ASTNode> p_relationalP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_relational();
unique_ptr<ASTNode> p_equalityP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_equality();
unique_ptr<ASTNode> p_logical_andP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_logical_and();
unique_ptr<ASTNode> p_logical_orP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_logical_or();
unique_ptr<ASTNode> p_expr();
unique_ptr<ASTNode> p_return_stmt();
unique_ptr<BlockASTNode> p_else_stmt();
unique_ptr<ASTNode> p_if_stmt();
unique_ptr<ASTNode> p_while_stmt();
unique_ptr<ASTNode> p_expr_stmt();
unique_ptr<ASTNode> p_stmt();
vector<unique_ptr<ASTNode>> p_stmt_listP(vector<unique_ptr<ASTNode>> &stmt_list);
vector<unique_ptr<ASTNode>> p_stmt_list();
unique_ptr<VarASTNode> p_local_decl();
vector<unique_ptr<VarASTNode>> p_local_declsP(vector<unique_ptr<VarASTNode>> &local_decls);
vector<unique_ptr<VarASTNode>> p_local_decls();
unique_ptr<BlockASTNode> p_block();
unique_ptr<VarASTNode> p_param();
vector<unique_ptr<VarASTNode>> p_param_listP(vector<unique_ptr<VarASTNode>> &param_list);
vector<unique_ptr<VarASTNode>> p_param_list();
vector<unique_ptr<VarASTNode>> p_params();
int p_var_type();
int p_type_spec();
unique_ptr<ASTNode> p_decl();
vector<unique_ptr<ASTNode>> p_decl_listP(vector<unique_ptr<ASTNode>> &decl_list);
vector<unique_ptr<ASTNode>> p_decl_list();
unique_ptr<ExternASTNode> p_extern();
vector<unique_ptr<ExternASTNode>> p_extern_listP(vector<unique_ptr<ExternASTNode>> &extern_list);
vector<unique_ptr<ExternASTNode>> p_extern_list();
unique_ptr<ProgramASTNode> p_program();

// arg_list' -> "," expr arg_list' | ϵ
vector<unique_ptr<ASTNode>> p_arg_listP(vector<unique_ptr<ASTNode>> &arg_list) {
  if (!match(COMMA)) {
    if (contains(follow_arg_listP, CurTok.type)) {
      return std::move(arg_list);
    } else {
      return {}; // Error
    }
  }
  unique_ptr<ASTNode> expr = p_expr();
  if (!expr) {
    return {}; // Error
  }
  arg_list.push_back(std::move(expr));

  return p_arg_listP(arg_list);
}

// arg_list -> expr arg_list'
vector<unique_ptr<ASTNode>> p_arg_list() {
  vector<unique_ptr<ASTNode>> arg_list;
  unique_ptr<ASTNode> expr = p_expr();
  if (!expr) {
    return {}; // Error
  }
  arg_list.push_back(std::move(expr));

  return p_arg_listP(arg_list);
}

// args -> arg_list | ϵ
vector<unique_ptr<ASTNode>> p_args() {
  if (!contains(first_args, CurTok.type)) {
    if (contains(follow_args, CurTok.type)) {
      return {};
    } else {
      return {}; // Error
    }
  }

  return p_arg_list();
}

// literal -> INT_LIT | FLOAT_LIT | BOOL_LIT
unique_ptr<ASTNode> p_literal() {
  TOKEN literal = CurTok;

  if (match(INT_LIT)) {
    return make_unique<IntASTNode>(literal, IntVal);
  } else if (match(FLOAT_LIT)) {
    return make_unique<FloatASTNode>(literal, FloatVal);
  } else if (match(BOOL_LIT)) {
    return make_unique<BoolASTNode>(literal, BoolVal);
  } else {
    return nullptr; // Error
  }
}

// reference' -> "(" args ")" | ϵ
vector<unique_ptr<ASTNode>> p_referenceP() {
  if (!match(LPAR)) {
    if (contains(follow_referenceP, CurTok.type)) {
      return {};
    } else {
      return {}; // Error
    }
  }
  vector<unique_ptr<ASTNode>> args = p_args();
  if (!match(RPAR)) {
    return {}; // Error
  }

  return args;
}

// reference -> IDENT reference' | literal
unique_ptr<ASTNode> p_reference() {
  TOKEN func = CurTok;
  if (!match(IDENT)) {
    if (contains(first_literal, CurTok.type)) {
      return p_literal();
    } else {
      return nullptr; // Error
    }
  }
  vector<unique_ptr<ASTNode>> args = p_referenceP();

  return make_unique<CallASTNode>(func, func.lexeme, std::move(args));
}

// factor -> "(" expr ")" | reference
unique_ptr<ASTNode> p_factor() {
  if (!match(LPAR)) {
    if (contains(first_reference, CurTok.type)) {
      return p_reference();
    } else {
      return nullptr; // Error
    }
  }
  unique_ptr<ASTNode> expr = p_expr();
  if (!expr) {
    return nullptr; // Error
  }
  if (!match(RPAR)) {
    return nullptr; // Error
  }

  return expr;
}

// unary -> "-" unary | "!" unary | factor
unique_ptr<ASTNode> p_unary() {
  TOKEN unaryOp = CurTok;
  if (!match(MINUS) && !match(NOT)) {
    if (contains(first_factor, CurTok.type)) {
      return p_factor();
    } else {
      return nullptr; // Error
    }
  }

  return make_unique<UnaryASTNode>(unaryOp, unaryOp.type, p_unary());
}

// multiplicative' -> "*" unary multiplicative' | "/" unary multiplicative' |
// "%" unary multiplicative' | ϵ
unique_ptr<ASTNode> p_multiplicativeP(unique_ptr<ASTNode> lhs) {
  TOKEN multiplicativeOp = CurTok;
  if (!match(ASTERIX) && !match(DIV) && !match(MOD)) {
    if (contains(follow_multiplicativeP, CurTok.type)) {
      return lhs;
    } else {
      return nullptr; // Error
    }
  }
  unique_ptr<BinaryASTNode> multiplicativeExpr = make_unique<BinaryASTNode>(
      multiplicativeOp, multiplicativeOp.type, std::move(lhs), p_unary());

  return p_multiplicativeP(std::move(multiplicativeExpr));
}

// multiplicative -> unary multiplicative'
unique_ptr<ASTNode> p_multiplicative() {
  unique_ptr<ASTNode> unary = p_unary();
  if (!unary) {
    return nullptr; // Error
  }

  return p_multiplicativeP(std::move(unary));
}

// additive' -> "+" multiplicative additive' | "-" multiplicative additive' | ϵ
unique_ptr<ASTNode> p_additiveP(unique_ptr<ASTNode> lhs) {
  TOKEN additiveOp = CurTok;
  if (!match(PLUS) && !match(MINUS)) {
    if (contains(follow_additiveP, CurTok.type)) {
      return lhs;
    } else {
      return nullptr; // Error
    }
  }
  unique_ptr<BinaryASTNode> additiveExpr = make_unique<BinaryASTNode>(
      additiveOp, additiveOp.type, std::move(lhs), p_multiplicative());

  return p_additiveP(std::move(additiveExpr));
}

// additive -> multiplicative additive'
unique_ptr<ASTNode> p_additive() {
  unique_ptr<ASTNode> multiplicativeExpr = p_multiplicative();
  if (!multiplicativeExpr) {
    return nullptr; // Error
  }

  return p_additiveP(std::move(multiplicativeExpr));
}

// relational' -> "<=" additive relational' | "<" additive relational' | ">="
// additive relational' | ">" additive relational' | ϵ
unique_ptr<ASTNode> p_relationalP(unique_ptr<ASTNode> lhs) {
  TOKEN relationalOp = CurTok;
  if (!match(LE) && !match(LT) && !match(GE) && !match(GT)) {
    if (contains(follow_relationalP, CurTok.type)) {
      return lhs;
    } else {
      return nullptr; // Error
    }
  }
  unique_ptr<BinaryASTNode> relationalExpr = make_unique<BinaryASTNode>(
      relationalOp, relationalOp.type, std::move(lhs), p_additive());

  return p_relationalP(std::move(relationalExpr));
}

// relational -> additive relational'
unique_ptr<ASTNode> p_relational() {
  unique_ptr<ASTNode> additiveExpr = p_additive();
  if (!additiveExpr) {
    return nullptr; // Error
  }

  return p_relationalP(std::move(additiveExpr));
}

// equality' -> "==" relational equality' | "!=" relational equality' | ϵ
unique_ptr<ASTNode> p_equalityP(unique_ptr<ASTNode> lhs) {
  TOKEN equalityOp = CurTok;
  if (!match(EQ) && !match(NE)) {
    if (contains(follow_equalityP, CurTok.type)) {
      return lhs;
    } else {
      return nullptr; // Error
    }
  }
  unique_ptr<BinaryASTNode> equalityExpr = make_unique<BinaryASTNode>(
      equalityOp, equalityOp.type, std::move(lhs), p_relational());

  return p_equalityP(std::move(equalityExpr));
}

// equality -> relational equality'
unique_ptr<ASTNode> p_equality() {
  unique_ptr<ASTNode> relationalExpr = p_relational();
  if (!relationalExpr) {
    return nullptr; // Error
  }

  return p_equalityP(std::move(relationalExpr));
}

// logical_and' -> "&&" equality logical_and' | ϵ
unique_ptr<ASTNode> p_logical_andP(unique_ptr<ASTNode> lhs) {
  TOKEN logicalAndOp = CurTok;
  if (!match(AND)) {
    if (contains(follow_logical_andP, CurTok.type)) {
      return lhs;
    } else {
      return nullptr; // Error
    }
  }
  unique_ptr<BinaryASTNode> logicalAndExpr = make_unique<BinaryASTNode>(
      logicalAndOp, logicalAndOp.type, std::move(lhs), p_equality());
  return p_logical_andP(std::move(logicalAndExpr));
}

// logical_and -> equality logical_and'
unique_ptr<ASTNode> p_logical_and() {
  unique_ptr<ASTNode> equalityExpr = p_equality();
  if (!equalityExpr) {
    return nullptr; // Error
  }

  return p_logical_andP(std::move(equalityExpr));
}

// logical_or' -> "||" logical_and logical_or' | ϵ
unique_ptr<ASTNode> p_logical_orP(unique_ptr<ASTNode> lhs) {
  TOKEN logicalOrOp = CurTok;
  if (!match(OR)) {
    if (contains(follow_logical_orP, CurTok.type)) {
      return lhs;
    } else {
      return nullptr; // Error
    }
  }
  unique_ptr<BinaryASTNode> logicalOrExpr = make_unique<BinaryASTNode>(
      logicalOrOp, logicalOrOp.type, std::move(lhs), p_logical_and());

  return p_logical_orP(std::move(logicalOrExpr));
}

// logical_or -> logical_and logical_or'
unique_ptr<ASTNode> p_logical_or() {
  unique_ptr<ASTNode> logicalAndExpr = p_logical_and();
  if (!logicalAndExpr) {
    return nullptr; // Error
  }

  return p_logical_orP(std::move(logicalAndExpr));
}

// expr -> IDENT "=" expr | logical_or
unique_ptr<ASTNode> p_expr() {
  TOKEN temp = CurTok;
  getNextToken();
  if (!(temp.type == IDENT) || !match(ASSIGN)) {
    if (contains(first_logical_or, temp.type)) {
      putBackToken(CurTok);
      CurTok = temp;
      return p_logical_or();
    } else {
      return nullptr; // Error
    }
  }
  unique_ptr<VarReferenceASTNode> var =
      make_unique<VarReferenceASTNode>(temp, temp.lexeme);
  unique_ptr<ASTNode> expr = p_expr();

  return make_unique<BinaryASTNode>(temp, ASSIGN, std::move(var), std::move(expr));
}

// return_stmt -> "return" expr_stmt
unique_ptr<ASTNode> p_return_stmt() {
  TOKEN returnTok = CurTok;
  if (!match(RETURN)) {
    return nullptr; // Error
  }

  unique_ptr<ASTNode> exprStmt = p_expr_stmt();
  if (!exprStmt) {
    return nullptr; // Error
  }

  return make_unique<ReturnASTNode>(returnTok, std::move(exprStmt));
}

// else_stmt -> "else" block | ϵ
unique_ptr<BlockASTNode> p_else_stmt() {
  TOKEN elseTok = CurTok;
  if (!match(ELSE)) {
    if (contains(follow_else_stmt, CurTok.type)) {
      return nullptr;
    } else {
      return nullptr; // Error
    }
  }
  unique_ptr<BlockASTNode> block = p_block();
  if (!block) {
    return nullptr; // Error
  }

  return block;
}

// if_stmt -> "if" "(" expr ")" block else_stmt
unique_ptr<ASTNode> p_if_stmt() {
  TOKEN ifTok = CurTok;
  if (!match(IF) || !match(LPAR)) {
    return nullptr; // Error
  }
  unique_ptr<ASTNode> cond = p_expr();
  if (!cond || !match(RPAR)) {
    return nullptr; // Error
  }
  unique_ptr<BlockASTNode> thenBlock = p_block();
  if (!thenBlock) {
    return nullptr; // Error
  }
  unique_ptr<BlockASTNode> elseStmt = p_else_stmt();

  return make_unique<IfASTNode>(ifTok, std::move(cond), std::move(thenBlock),
                                std::move(elseStmt));
}

// while_stmt -> "while" "(" expr ")" stmt
unique_ptr<ASTNode> p_while_stmt() {
  TOKEN whileTok = CurTok;
  if (!match(WHILE) || !match(LPAR)) {
    return nullptr; // Error
  }
  unique_ptr<ASTNode> expr = p_expr();
  if (!expr || !match(RPAR)) {
    return nullptr; // Error
  }
  unique_ptr<ASTNode> stmt = p_stmt();
  if (!stmt) {
    return nullptr; // Error
  }

  return make_unique<WhileASTNode>(whileTok, std::move(expr), std::move(stmt));
}

// expr_stmt -> expr ";" | ";"
unique_ptr<ASTNode> p_expr_stmt() {
  if (!contains(first_expr, CurTok.type)) {
    if (!match(SC)) {
      return nullptr; // Error
    }
    return nullptr;
  }
  unique_ptr<ASTNode> expr = p_expr();
  if (!expr || !match(SC)) {
    return nullptr; // Error
  }

  return expr;
}

// stmt -> expr_stmt | block | if_stmt | while_stmt | return_stmt
unique_ptr<ASTNode> p_stmt() {
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
    return nullptr; // Error
  }
}

// stmt_list' -> stmt stmt_list' | ϵ
vector<unique_ptr<ASTNode>>
p_stmt_listP(vector<unique_ptr<ASTNode>> &stmt_list) {
  if (!contains(first_stmt, CurTok.type)) {
    if (contains(follow_stmt_listP, CurTok.type)) {
      return std::move(stmt_list);
    } else {
      return {}; // Error
    }
  }
  unique_ptr<ASTNode> stmt = p_stmt();
  if (!stmt) {
    return {}; // Error
  }
  stmt_list.push_back(std::move(stmt));

  return p_stmt_listP(stmt_list);
}

// stmt_list -> stmt stmt_list'
vector<unique_ptr<ASTNode>> p_stmt_list() {
  vector<unique_ptr<ASTNode>> stmt_list;
  unique_ptr<ASTNode> stmt = p_stmt();
  if (!stmt) {
    return {}; // Error
  }
  stmt_list.push_back(std::move(stmt));

  return p_stmt_listP(stmt_list);
}

// local_decl -> var_type IDENT ";"
unique_ptr<VarASTNode> p_local_decl() {
  int varType = p_var_type();
  if (varType == 0) {
    return nullptr; // Error
  }
  TOKEN varName = CurTok;
  if (!match(IDENT) || !match(SC)) {
    return nullptr; // Error
  }

  return make_unique<VarASTNode>(varName, varType, varName.lexeme);
}

// local_decls' -> local_decl local_decls' | ϵ
vector<unique_ptr<VarASTNode>>
p_local_declsP(vector<unique_ptr<VarASTNode>> &local_decls) {
  if (!contains(first_local_decl, CurTok.type)) {
    if (contains(follow_local_declsP, CurTok.type)) {
      return std::move(local_decls);
    } else {
      return {}; // Error
    }
  }
  unique_ptr<VarASTNode> localDecl = p_local_decl();
  if (!localDecl) {
    return {}; // Error
  }
  local_decls.push_back(std::move(localDecl));

  return p_local_declsP(local_decls);
}

// local_decls -> local_decls'
vector<unique_ptr<VarASTNode>> p_local_decls() {
  vector<unique_ptr<VarASTNode>> local_decls;

  return p_local_declsP(local_decls);
}

// block -> "{" local_decls stmt_list "}"
unique_ptr<BlockASTNode> p_block() {
  if (!match(LBRA)) {
    return nullptr; // Error
  }
  vector<unique_ptr<VarASTNode>> localDecls = p_local_decls();
  vector<unique_ptr<ASTNode>> stmtList = p_stmt_list();
  if (!match(RBRA)) {
    return nullptr; // Error
  }

  return make_unique<BlockASTNode>(std::move(localDecls), std::move(stmtList));
}

// param -> var_type IDENT
unique_ptr<VarASTNode> p_param() {
  int varType = p_var_type();
  if (varType == 0) {
    return nullptr; // Error
  }
  TOKEN varName = CurTok;
  if (!match(IDENT)) {
    return nullptr; // Error
  }

  return make_unique<VarASTNode>(varName, varType, varName.lexeme);
}

// param_list' -> "," param param_list' | ϵ
vector<unique_ptr<VarASTNode>>
p_param_listP(vector<unique_ptr<VarASTNode>> &param_list) {
  if (!match(COMMA)) {
    if (contains(follow_param_listP, CurTok.type)) {
      return std::move(param_list);
    } else {
      return {}; // Error
    }
  }
  unique_ptr<VarASTNode> param = p_param();
  if (!param) {
    return {}; // Error
  }
  param_list.push_back(std::move(param));

  return p_param_listP(param_list);
}

// param_list -> param param_list'
vector<unique_ptr<VarASTNode>> p_param_list() {
  vector<unique_ptr<VarASTNode>> param_list;
  unique_ptr<VarASTNode> param = p_param();
  if (!param) {
    return {}; // Error
  }
  param_list.push_back(std::move(param));

  return p_param_listP(param_list);
}

// params -> param_list | "void" | ϵ
vector<unique_ptr<VarASTNode>> p_params() {
  if (!contains(first_params, CurTok.type)) {
    if (contains(follow_params, CurTok.type)) {
      return {}; // Void, no parameters
    } else {
      return {}; // Error
    }
  }

  return p_param_list();
}

// var_type -> "int" | "float" | "bool"
int p_var_type() {
  if (match(INT_TOK)) {
    return INT_TOK;
  } else if (match(FLOAT_TOK)) {
    return FLOAT_TOK;
  } else if (match(BOOL_TOK)) {
    return BOOL_TOK;
  } else {
    return 0; // Error
  }
}

// type_spec -> var_type | "void"
int p_type_spec() {
  if (contains(first_var_type, CurTok.type)) {
    return p_var_type();
  } else if (match(VOID_TOK)) {
    return VOID_TOK;
  } else {
    return 0; // Error
  }
}

// decl -> var_type IDENT ";" | type_spec IDENT "(" params ")" block
unique_ptr<ASTNode> p_decl() {
  if (!contains(first_var_type, CurTok.type) && !contains(first_type_spec, CurTok.type)) {
    return nullptr; // Error
  }
  int declType = p_var_type();
  if (declType == 0) {
    declType = p_type_spec();
    if (declType == 0) {
      return nullptr; // Error
    }
  }
  TOKEN declName = CurTok;
  if (!match(IDENT)) {
    return nullptr; // Error
  }
  if (match(SC)) {
    return make_unique<VarASTNode>(declName, declType, declName.lexeme);
  }
  if (!match(LPAR)) {
    return nullptr; // Error
  }
  vector<unique_ptr<VarASTNode>> params = p_params();
  if (!match(RPAR)) {
    return nullptr; // Error
  }
  unique_ptr<BlockASTNode> block = p_block();
  if (!block) {
    return nullptr; // Error
  }

  return make_unique<FunctionASTNode>(declType, declName.lexeme, std::move(params), std::move(block));
}

// decl_list' -> decl decl_list' | ϵ
vector<unique_ptr<ASTNode>> p_decl_listP(vector<unique_ptr<ASTNode>> &decl_list) {
  if (!contains(first_decl, CurTok.type)) {
    if (contains(follow_decl_listP, CurTok.type)) {
      return std::move(decl_list);
    } else {
      return {}; // Error
    }
  }
  unique_ptr<ASTNode> decl = p_decl();
  if (!decl) {
    return {}; // Error
  }
  decl_list.push_back(std::move(decl));

  return p_decl_listP(decl_list);
}

// decl_list -> decl decl_list'
vector<unique_ptr<ASTNode>> p_decl_list() {
  vector<unique_ptr<ASTNode>> decl_list;

  return p_decl_listP(decl_list);
}

// extern -> "extern" type_spec IDENT "(" params ")" ";"
unique_ptr<ExternASTNode> p_extern() {
  if (!match(EXTERN)) {
    return nullptr; // Error
  }
  int externType = p_type_spec();
  if (externType == 0) {
    return nullptr; // Error
  }
  TOKEN externName = CurTok;
  if (!match(IDENT) || !match(LPAR)) {
    return nullptr; // Error
  }
  vector<unique_ptr<VarASTNode>> params = p_params();
  if (!match(RPAR) || !match(SC)) {
    return nullptr; // Error
  }

  return make_unique<ExternASTNode>(externName.lexeme, std::move(params));
}

// extern_list' -> extern extern_list' | ϵ
vector<unique_ptr<ExternASTNode>> p_extern_listP(vector<unique_ptr<ExternASTNode>> &extern_list) {
  if (!contains(first_extern, CurTok.type)) {
    if (contains(follow_extern_listP, CurTok.type)) {
      return std::move(extern_list);
    } else {
      return {}; // Error
    }
  }
  unique_ptr<ExternASTNode> externDecl = p_extern();
  if (!externDecl) {
    return {}; // Error
  }
  extern_list.push_back(std::move(externDecl));

  return p_extern_listP(extern_list);
}

// extern_list -> extern extern_list'
vector<unique_ptr<ExternASTNode>> p_extern_list() {
  vector<unique_ptr<ExternASTNode>> extern_list;

  return p_extern_listP(extern_list);
}

// program -> extern_list decl_list | decl_list
unique_ptr<ProgramASTNode> p_program() {
  if (contains(first_extern_list, CurTok.type)) {
    vector<unique_ptr<ExternASTNode>> externs = p_extern_list();
    vector<unique_ptr<ASTNode>> decls = p_decl_list();

    return make_unique<ProgramASTNode>(std::move(externs), std::move(decls));
  } else if (contains(first_decl_list, CurTok.type)) {
    vector<unique_ptr<ExternASTNode>> externs;
    vector<unique_ptr<ASTNode>> decls = p_decl_list();
  
    return make_unique<ProgramASTNode>(std::move(externs), std::move(decls));
  } else {
    return nullptr;
  }
}

static unique_ptr<ProgramASTNode> parser() {
  getNextToken(); // Consume EOF
  unique_ptr<ProgramASTNode> program;

  if ((program = p_program()) != nullptr && CurTok.type == EOF_TOK) {
    fprintf(stderr, "Parsing Successful\n");
    return program;
  } else {
    fprintf(stderr, "Parsing Failed\n");
    return nullptr;
  }
}

//===----------------------------------------------------------------------===//
// `Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static unique_ptr<Module> TheModule;

Value *IntASTNode::codegen() {
  return nullptr;
}

Value *FloatASTNode::codegen() {
  return nullptr;
}

Value *BoolASTNode::codegen() {
  return nullptr;
}

Value *VarASTNode::codegen() {
  return nullptr;
}

Value *VarReferenceASTNode::codegen() {
  return nullptr;
}

Value *CallASTNode::codegen() {
  return nullptr;
}

Value *UnaryASTNode::codegen() {
  return nullptr;
}

Value *BinaryASTNode::codegen() {
  return nullptr;
}

Value *ReturnASTNode::codegen() {
  return nullptr;
}

Value *IfASTNode::codegen() {
  return nullptr;
}

Value *WhileASTNode::codegen() {
  return nullptr;
}

Value *BlockASTNode::codegen() {
  return nullptr;
}

Value *FunctionASTNode::codegen() {
  return nullptr;
}

Value *ExternASTNode::codegen() {
  return nullptr;
}

Value *ProgramASTNode::codegen() {
  return nullptr;
}

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const ASTNode &ast) {
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
    cout << "Usage: ./code InputFile\n";
    return 1;
  }

  // initialize line number and column numbers to zero
  lineNo = 1;
  columnNo = 1;

  // get the first token
  // getNextToken();
  // while (CurTok.type != EOF_TOK) {
  //  fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
  //          CurTok.type);
  //  getNextToken();
  //}
  // fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = make_unique<Module>("mini-c", TheContext);

  // Run the parser now.
  parser();
  fprintf(stderr, "Parsing Finished\n");

  //********************* Start printing final IR **************************
  // Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  error_code EC;
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
