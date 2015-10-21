package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.*;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class SSAVisitor extends SimpleCBaseVisitor<String> {
    private final SSAMap ssaMap;

    public SSAVisitor() {
        ssaMap = new SSAMap();
    }

    @Override
    public String visitProgram(ProgramContext ctx) {
        return null;
    }

    @Override
    public String visitVarDecl(VarDeclContext ctx) {
        String var = ctx.ident.name.getText();
        return SMTUtil.declare(var, ssaMap.id(var));
    }

    @Override
    public String visitProcedureDecl(ProcedureDeclContext ctx) {
        StringBuilder result = new StringBuilder();

        for (StmtContext stmtContext : ctx.stmt()) {
            result.append(visit(stmtContext));
        }

        return result.toString();
    }

    @Override
    public String visitFormalParam(FormalParamContext ctx) {
        return null;
    }

    @Override
    public String visitPrepost(PrepostContext ctx) {
        return null;
    }

    @Override
    public String visitRequires(RequiresContext ctx) {
        return null;
    }

    @Override
    public String visitEnsures(EnsuresContext ctx) {
        return null;
    }

    @Override
    public String visitCandidateRequires(CandidateRequiresContext ctx) {
        return null;
    }

    @Override
    public String visitCandidateEnsures(CandidateEnsuresContext ctx) {
        return null;
    }

    @Override
    public String visitStmt(StmtContext ctx) {
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
    public String visitAssignStmt(AssignStmtContext ctx) {
        String var = ctx.lhs.ident.name.getText();
        int id = ssaMap.fresh(var);
        String rhs = visit(ctx.rhs);

        StringBuilder result = new StringBuilder();
        result.append(SMTUtil.declare(var, id));
        result.append(SMTUtil.assertion("=", var + id, rhs));
        ssaMap.update(var, id);

        return result.toString();
    }

    @Override
    public String visitAssertStmt(AssertStmtContext ctx) {
        return SMTUtil.assertion("not", visitExpr(ctx.expr()));
    }

    @Override
    public String visitAssumeStmt(AssumeStmtContext ctx) {
        return null;
    }

    @Override
    public String visitHavocStmt(HavocStmtContext ctx) {
        return null;
    }

    @Override
    public String visitCallStmt(CallStmtContext ctx) {
        return null;
    }

    @Override
    public String visitIfStmt(IfStmtContext ctx) {
        return null;
    }

    @Override
    public String visitWhileStmt(WhileStmtContext ctx) {
        return null;
    }

    @Override
    public String visitBlockStmt(BlockStmtContext ctx) {
        return null;
    }

    @Override
    public String visitLoopInvariant(LoopInvariantContext ctx) {
        return null;
    }

    @Override
    public String visitInvariant(InvariantContext ctx) {
        return null;
    }

    @Override
    public String visitCandidateInvariant(CandidateInvariantContext ctx) {
        return null;
    }

    @Override
    public String visitExpr(ExprContext ctx) {
        if (ctx.ternExpr() != null) {
            return visit(ctx.ternExpr());
        }

        return null;
    }

    @Override
    public String visitTernExpr(TernExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.args != null) {
            for (LorExprContext lorExprContext : ctx.args) {
                result.append(visit(lorExprContext));
            }
        }

        return result.toString();
    }

    @Override
    public String visitLorExpr(LorExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.args != null) {
            for (LandExprContext landExprContext : ctx.args) {
                result.append(visit(landExprContext));
            }
        }

        return result.toString();
    }

    @Override
    public String visitLandExpr(LandExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.args != null) {
            for (BorExprContext borExprContext : ctx.args) {
                result.append(visit(borExprContext));
            }
        }

        return result.toString();
    }

    @Override
    public String visitBorExpr(BorExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.args != null) {
            for (BxorExprContext bxorExprContext : ctx.args) {
                result.append(visit(bxorExprContext));
            }
        }

        return result.toString();
    }

    @Override
    public String visitBxorExpr(BxorExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.args != null) {
            for (BandExprContext bandExprContext : ctx.args) {
                result.append(visit(bandExprContext));
            }
        }

        return result.toString();
    }

    @Override
    public String visitBandExpr(BandExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.args != null) {
            for (EqualityExprContext equalityExprContext : ctx.args) {
                result.append(visit(equalityExprContext));
            }
        }

        return result.toString();
    }

    @Override
    public String visitEqualityExpr(EqualityExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
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

        return result.toString();
    }

    @Override
    public String visitRelExpr(RelExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.args != null) {
            for (ShiftExprContext shiftExprContext : ctx.args) {
                result.append(visit(shiftExprContext));
            }
        }

        return result.toString();
    }

    @Override
    public String visitShiftExpr(ShiftExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.args != null) {
            for (AddExprContext addExprContext : ctx.args) {
                result.append(visit(addExprContext));
            }
        }

        return result.toString();
    }

    @Override
    public String visitAddExpr(AddExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.args != null) {
            List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
            List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertOperator(op.getText())).collect(Collectors.toList());
            return SMTUtil.expression(args, operators);
        }

        return result.toString();
    }

    @Override
    public String visitMulExpr(MulExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
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

        return result.toString();
    }

    @Override
    public String visitUnaryExpr(UnaryExprContext ctx) {
        StringBuilder result = new StringBuilder();

        if (ctx.single != null) {
            result.append(visit(ctx.single));
        } else if (ctx.arg != null) {
            result.append(visit(ctx.arg));
        }

        return result.toString();
    }

    @Override
    public String visitAtomExpr(AtomExprContext ctx) {
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

        return result.toString();
    }

    @Override
    public String visitNumberExpr(NumberExprContext ctx) {
        return ctx.NUMBER().toString();
    }

    @Override
    public String visitVarrefExpr(VarrefExprContext ctx) {
        StringBuilder result = new StringBuilder();

        String varName = ctx.var.ident.name.getText();
        Integer varID = ssaMap.id(varName);

        result.append(varName + varID);

        return result.toString();
    }

    @Override
    public String visitParenExpr(ParenExprContext ctx) {
        return null;
    }

    @Override
    public String visitResultExpr(ResultExprContext ctx) {
        return null;
    }

    @Override
    public String visitOldExpr(OldExprContext ctx) {
        return null;
    }

    @Override
    public String visitVarref(VarrefContext ctx) {
        return null;
    }

    @Override
    public String visitVarIdentifier(VarIdentifierContext ctx) {
        return null;
    }
}
