// libFuzzer harness for the BoogieAst printers.
//
// SMACK's Boogie output goes through Expr/Stmt/Decl ::print(ostream&).
// A crash in any printer reachable from fuzzer-controlled AST shape
// would surface as a verifier abort on real inputs. This harness uses
// the fuzzer bytes as a small program: bytes pick which factory to
// call, identifiers are derived from the byte values, then we print
// the resulting AST and discard it. The printers must tolerate any
// shape we construct without crashing.

#include "smack/BoogieAst.h"

#include <cstddef>
#include <cstdint>
#include <sstream>
#include <string>

using namespace smack;

namespace {

struct Cursor {
  const uint8_t *data;
  size_t size;
  size_t pos;

  uint8_t next(uint8_t fallback = 0) {
    if (pos >= size)
      return fallback;
    return data[pos++];
  }

  std::string ident(uint8_t hint) {
    // Keep identifier chars in [a-z0-9_] so the printer doesn't have to
    // escape — we're fuzzing the printer, not the lexer.
    static const char alphabet[] = "abcdefghijklmnopqrstuvwxyz0123456789_";
    std::string s;
    s.push_back(alphabet[hint % (sizeof(alphabet) - 1)]);
    s.push_back(alphabet[next() % (sizeof(alphabet) - 1)]);
    return s;
  }
};

const Expr *makeExpr(Cursor &c, unsigned depth) {
  if (depth == 0 || c.pos >= c.size)
    return Expr::lit(true);

  uint8_t op = c.next();
  switch (op % 9) {
  case 0:
    return Expr::lit(true);
  case 1:
    return Expr::lit(false);
  case 2:
    return Expr::lit(static_cast<long long>(c.next()));
  case 3:
    return Expr::id(c.ident(op));
  case 4:
    return Expr::and_(makeExpr(c, depth - 1), makeExpr(c, depth - 1));
  case 5:
    return Expr::or_(makeExpr(c, depth - 1), makeExpr(c, depth - 1));
  case 6:
    return Expr::not_(makeExpr(c, depth - 1));
  case 7:
    return Expr::eq(makeExpr(c, depth - 1), makeExpr(c, depth - 1));
  case 8:
  default:
    return Expr::impl(makeExpr(c, depth - 1), makeExpr(c, depth - 1));
  }
}

const Stmt *makeStmt(Cursor &c, unsigned depth) {
  if (depth == 0 || c.pos >= c.size)
    return Stmt::skip();

  uint8_t op = c.next();
  switch (op % 6) {
  case 0:
    return Stmt::assert_(makeExpr(c, depth - 1));
  case 1:
    return Stmt::assume(makeExpr(c, depth - 1));
  case 2:
    return Stmt::havoc(c.ident(op));
  case 3:
    return Stmt::comment(c.ident(op));
  case 4:
    return Stmt::goto_({c.ident(op), c.ident(op)});
  case 5:
  default:
    return Stmt::return_();
  }
}

} // namespace

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, std::size_t size) {
  if (size < 2)
    return 0;

  Cursor c{data, size, 0};

  // Build a handful of small AST shapes and print each.
  std::ostringstream sink;
  const unsigned exprBatch = (c.next() % 4) + 1;
  for (unsigned i = 0; i < exprBatch; ++i) {
    const Expr *e = makeExpr(c, /*depth=*/3);
    e->print(sink);
    sink << '\n';
  }

  const unsigned stmtBatch = (c.next() % 4) + 1;
  for (unsigned i = 0; i < stmtBatch; ++i) {
    const Stmt *s = makeStmt(c, /*depth=*/2);
    s->print(sink);
    sink << '\n';
  }

  // Block + ProcDecl wrappers — exercise the container print paths too.
  Block *b = Block::block(c.ident(0xab), {makeStmt(c, /*depth=*/2)});
  b->print(sink);

  ProcDecl *p = Decl::procedure(c.ident(0xcd));
  p->getRequires().push_back(makeExpr(c, /*depth=*/2));
  p->print(sink);

  return 0;
}
