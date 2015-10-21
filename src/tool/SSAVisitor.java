package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.*;

public class SSAVisitor extends SimpleCBaseVisitor<StringBuilder> {

    private SSAMap ssaMap;

    public SSAVisitor() {
        ssaMap = new SSAMap();
    }

    @Override
    public StringBuilder visitProgram(ProgramContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitVarDecl(VarDeclContext ctx) {
        StringBuilder result = new StringBuilder();

        // String varName = ctx.ident.name.getText();
        // Integer varID = ssaMap.getNextID(varName);

        // result.append("(declare-fun " + varName + varID + " () (_ BitVec 32))\n");

        return result;
    }

    @Override
    public StringBuilder visitProcedureDecl(ProcedureDeclContext ctx) {
        StringBuilder result = new StringBuilder();

        for (StmtContext stmtContext : ctx.stmt()) {
            result.append(visit(stmtContext));
        }

        return result;
    }

    @Override
    public StringBuilder visitFormalParam(FormalParamContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitPrepost(PrepostContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitRequires(RequiresContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitEnsures(EnsuresContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitCandidateRequires(CandidateRequiresContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitCandidateEnsures(CandidateEnsuresContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitStmt(StmtContext ctx) {
        if (ctx.varDecl() != null) {
            return visit(ctx.varDecl());
        }

        if (ctx.assignStmt() != null) {
            return visit(ctx.assignStmt());
        }

        if (ctx.assertStmt() != null) {
            return visit(ctx.assertStmt());
        }

        return null;
    }

    @Override
    public StringBuilder visitAssignStmt(AssignStmtContext ctx) {
        StringBuilder result = new StringBuilder();

        String varName = ctx.lhs.ident.name.getText();
        Integer varID = ssaMap.getNextID(varName);
        StringBuilder rhsExpr = visit(ctx.rhs);

        // First declare the new variable.
        result.append("(declare-fun " + varName + varID + " () (_ BitVec 32))\n");

        // Then state the assignment.
        result.append("(assert (= " + varName + varID + " " + rhsExpr + "))\n");

        return result;
    }

    @Override
    public StringBuilder visitAssertStmt(AssertStmtContext ctx) {
        StringBuilder result = new StringBuilder();

        result.append("(assert (not " + visit(ctx.expr()) + "))\n");

        return result;
    }

    @Override
    public StringBuilder visitAssumeStmt(AssumeStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitHavocStmt(HavocStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitCallStmt(CallStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitIfStmt(IfStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitWhileStmt(WhileStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitBlockStmt(BlockStmtContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitLoopInvariant(LoopInvariantContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitInvariant(InvariantContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitCandidateInvariant(CandidateInvariantContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitExpr(ExprContext ctx) {
        if (ctx.ternExpr() != null) {
            return visit(ctx.ternExpr());
        }

        return null;
    }

    @Override
    public StringBuilder visitTernExpr(TernExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            for (LorExprContext lorExprContext : ctx.args) {
                result.append(visit(lorExprContext));
            }
        }

        return result;
    }

    @Override
    public StringBuilder visitLorExpr(LorExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            for (LandExprContext landExprContext : ctx.args) {
                result.append(visit(landExprContext));
            }
        }

        return result;
    }

    @Override
    public StringBuilder visitLandExpr(LandExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            for (BorExprContext borExprContext : ctx.args) {
                result.append(visit(borExprContext));
            }
        }

        return result;
    }

    @Override
    public StringBuilder visitBorExpr(BorExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            for (BxorExprContext bxorExprContext : ctx.args) {
                result.append(visit(bxorExprContext));
            }
        }

        return result;
    }

    @Override
    public StringBuilder visitBxorExpr(BxorExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            for (BandExprContext bandExprContext : ctx.args) {
                result.append(visit(bandExprContext));
            }
        }

        return result;
    }

    @Override
    public StringBuilder visitBandExpr(BandExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            for (EqualityExprContext equalityExprContext : ctx.args) {
                result.append(visit(equalityExprContext));
            }
        }

        return result;
    }

    @Override
    public StringBuilder visitEqualityExpr(EqualityExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            result.append("(");
            int opIndex = 0;

            for ( ; opIndex < ctx.ops.size(); ++opIndex) {
                switch (ctx.ops.get(opIndex).getText()) {
                    case "==":
                        result.append("= ");
                        break;
                    case "!=":
                        result.append("distinct ");
                        break;
                    default:
                        break;
                }

                result.append(visit(ctx.args.get(opIndex)));
                result.append(" ");
            }

            // Append the last expression.
            result.append(visit(ctx.args.get(opIndex)));
            result.append(")");
        }

        return result;
    }

    @Override
    public StringBuilder visitRelExpr(RelExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            for (ShiftExprContext shiftExprContext : ctx.args) {
                result.append(visit(shiftExprContext));
            }
        }

        return result;
    }

    @Override
    public StringBuilder visitShiftExpr(ShiftExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            for (AddExprContext addExprContext : ctx.args) {
                result.append(visit(addExprContext));
            }
        }

        return result;
    }

    @Override
    public StringBuilder visitAddExpr(AddExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {
            result.append("(");
            int opIndex = 0;

            for ( ; opIndex < ctx.ops.size(); ++opIndex) {
                switch (ctx.ops.get(opIndex).getText()) {
                    case "+":
                        result.append("bvadd ");
                        break;
                    case "-":
                        result.append("bvsub ");
                        break;
                    default:
                        break;
                }

                result.append(visit(ctx.args.get(opIndex)));
                result.append(" ");
            }

            // Append the last expression.
            result.append(visit(ctx.args.get(opIndex)));
            result.append(")");
        }

        return result;
    }

    @Override
    public StringBuilder visitMulExpr(MulExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.args != null) {

            result.append("(");
            int opIndex = 0;

            for ( ; opIndex < ctx.ops.size(); ++opIndex) {
                switch (ctx.ops.get(opIndex).getText()) {
                    case "*":
                        result.append("bvmul ");
                        break;
                    case "/":
                        result.append("bvsdiv ");
                        break;
                    case "%":
                        result.append("bvmod ");
                    default:
                        break;
                }

                result.append(visit(ctx.args.get(opIndex)));
                result.append(" ");
            }

            // Append the last expression.
            result.append(visit(ctx.args.get(opIndex)));
            result.append(")");
        }

        return result;
    }

    @Override
    public StringBuilder visitUnaryExpr(UnaryExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result = visit(ctx.single);
        } else if (ctx.arg != null) {
            result = visit(ctx.arg);
        }

        return result;
    }

    @Override
    public StringBuilder visitAtomExpr(AtomExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.numberExpr() != null) {
            result.append("(_ bv" + visit(ctx.numberExpr()) + " 32)");
        }

        if (ctx.varrefExpr() != null) {
            result.append(visit(ctx.varrefExpr()));
        }

        if (ctx.parenExpr() != null) {
            // TODO:
        }

        if (ctx.resultExpr() != null) {
            // TODO:
        }

        if (ctx.oldExpr() != null) {
            // TODO:
        }

        return result;
    }

    @Override
    public StringBuilder visitNumberExpr(NumberExprContext ctx) {
        StringBuilder result = new StringBuilder();
        result.append(ctx.NUMBER());

        return result;
    }

    @Override
    public StringBuilder visitVarrefExpr(VarrefExprContext ctx) {
        StringBuilder result = new StringBuilder();

        String varName = ctx.var.ident.name.getText();
        Integer varID = ssaMap.getCurrentID(varName);

        result.append(varName + varID);

        return result;
    }

    @Override
    public StringBuilder visitParenExpr(ParenExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitResultExpr(ResultExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitOldExpr(OldExprContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitVarref(VarrefContext ctx) {
        return null;
    }

    @Override
    public StringBuilder visitVarIdentifier(VarIdentifierContext ctx) {
        return null;
    }

}
