package ast;

import visitor.VisitStage;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import parser.SimpleCParser;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class ASTBuilder {

    public static Program build(SimpleCParser.ProgramContext program) {
        List<VarDeclStmt> globalDecls = Lists.newArrayList();
        List<ProcedureDecl> procedureDecls = Lists.newArrayList();
        for (int i = 0; i < program.getChildCount(); ++i) {
            ParseTree child = program.getChild(i);
            if (child instanceof SimpleCParser.VarDeclContext) {
                globalDecls.add(build((SimpleCParser.VarDeclContext) child));
            } else if (child instanceof SimpleCParser.ProcedureDeclContext) {
                procedureDecls.add(build((SimpleCParser.ProcedureDeclContext) child));
            } else {
                throw new IllegalStateException(String.format(
                    "Program not well-formed: [%s] should not be part of program", child.toStringTree()));
            }
        }
        return new Program(globalDecls, procedureDecls);
    }

    private static VarDeclStmt build(SimpleCParser.VarDeclContext varDecl) {
        return new VarDeclStmt(new VarRef(varDecl.ident.name.getText()));
    }

    private static ProcedureDecl build(SimpleCParser.ProcedureDeclContext procedureDecl) {
        String name = procedureDecl.name.getText();
        List<VarRef> params = procedureDecl.formals.stream()
                .map(formal -> new VarRef(formal.ident.name.getText()))
                .collect(Collectors.toList());
        List<PrePostCondition> conditions = procedureDecl.contract.stream()
            .map(ASTBuilder::build)
            .collect(Collectors.toList());
        List<Stmt> stmts = procedureDecl.stmts.stream()
            .map(ASTBuilder::build)
            .collect(Collectors.toList());
        Expr returnExpr = build(procedureDecl.returnExpr);
        return new ProcedureDecl(name, params, conditions, stmts, returnExpr);
    }

    private static PrePostCondition build(SimpleCParser.PrepostContext prePost) {
        if (prePost.requires() != null) {
            return new Precondition(build(prePost.requires().condition));
        } else if (prePost.ensures() != null) {
            return new Postcondition(build(prePost.ensures().condition));
        } else if (prePost.candidateRequires() != null) {
            return new CandidatePrecondition(
                build(prePost.candidateRequires().condition),
                Optional.empty(),
                VisitStage.DIRTY);
        } else {
            return new CandidatePostcondition(
                build(prePost.candidateEnsures().condition),
                Optional.empty(),
                VisitStage.DIRTY);
        }
    }

    private static Stmt build(SimpleCParser.StmtContext stmt) {
        if (stmt.varDecl() != null) {
            return build(stmt.varDecl());
        } else if (stmt.assignStmt() != null) {
            return build(stmt.assignStmt());
        } else if (stmt.assertStmt() != null) {
            return build(stmt.assertStmt());
        } else if (stmt.assumeStmt() != null) {
            return build(stmt.assumeStmt());
        } else if (stmt.havocStmt() != null) {
            return build(stmt.havocStmt());
        } else if (stmt.callStmt() != null) {
            return build(stmt.callStmt());
        } else if (stmt.ifStmt() != null) {
            return build(stmt.ifStmt());
        } else if (stmt.whileStmt() != null) {
            return build(stmt.whileStmt());
        } else {
            return build(stmt.blockStmt());
        }
    }

    private static AssignStmt build(SimpleCParser.AssignStmtContext assignStmt) {
        return new AssignStmt(build(assignStmt.lhs), build(assignStmt.rhs));
    }

    private static AssertStmt build(SimpleCParser.AssertStmtContext assertStmt) {
        return new AssertStmt(build(assertStmt.condition), Optional.empty());
    }

    private static AssumeStmt build(SimpleCParser.AssumeStmtContext assumeStmt) {
        return new AssumeStmt(build(assumeStmt.condition));
    }

    private static HavocStmt build(SimpleCParser.HavocStmtContext havocStmt) {
        return new HavocStmt(build(havocStmt.var));
    }

    private static CallStmt build(SimpleCParser.CallStmtContext callStmt) {
        List<Expr> exprs = callStmt.actuals.stream().map(ASTBuilder::build).collect(Collectors.toList());
        return new CallStmt(build(callStmt.lhs), new ProcedureRef(callStmt.callee.getText()), exprs);
    }

    private static IfStmt build(SimpleCParser.IfStmtContext ifStmt) {
        Optional<BlockStmt> elseBlock = ifStmt.elseBlock != null
            ? Optional.of(build(ifStmt.elseBlock))
            : Optional.empty();
        return new IfStmt(build(ifStmt.condition), build(ifStmt.thenBlock), elseBlock);
    }

    private static WhileStmt build(SimpleCParser.WhileStmtContext whileStmt) {
        List<LoopInvariant> invariants = whileStmt.invariantAnnotations.stream()
            .map(ASTBuilder::build)
            .collect(Collectors.toList());
        return new WhileStmt(build(whileStmt.condition), build(whileStmt.body), invariants);
    }

    private static BlockStmt build(SimpleCParser.BlockStmtContext blockStmt) {
        return new BlockStmt(blockStmt.stmts.stream().map(ASTBuilder::build).collect(Collectors.toList()));
    }

    private static LoopInvariant build(SimpleCParser.LoopInvariantContext loopInvariant) {
        if (loopInvariant.invariant() != null) {
            return new Invariant(build(loopInvariant.invariant().condition));
        } else {
            return new CandidateInvariant(
                build(loopInvariant.candidateInvariant().condition),
                Optional.empty(),
                VisitStage.DIRTY);
        }
    }

    private static Expr build(SimpleCParser.ExprContext expr) {
        return build(expr.ternExpr());
    }

    private static Expr build(SimpleCParser.TernExprContext ternExpr) {
        if (ternExpr.single != null) {
            return build(ternExpr.single);
        }
        return unflattenTernaryExpr(ternExpr.args);
    }

    private static Expr build(SimpleCParser.LorExprContext lorExpr) {
        if (lorExpr.single != null) {
            return build(lorExpr.single);
        }
        return unflattenLandExpr(lorExpr.args, lorExpr.ops);
    }

    private static Expr build(SimpleCParser.LandExprContext landExpr) {
        if (landExpr.single != null) {
            return build(landExpr.single);
        }
        return unflattenBorExpr(landExpr.args, landExpr.ops);
    }

    private static Expr build(SimpleCParser.BorExprContext borExpr) {
        if (borExpr.single != null) {
            return build(borExpr.single);
        }
        return unflattenBxorExpr(borExpr.args, borExpr.ops);
    }

    private static Expr build(SimpleCParser.BxorExprContext bxorExpr) {
        if (bxorExpr.single != null) {
            return build(bxorExpr.single);
        }
        return unflattenBandExpr(bxorExpr.args, bxorExpr.ops);
    }

    private static Expr build(SimpleCParser.BandExprContext bandExpr) {
        if (bandExpr.single != null) {
            return build(bandExpr.single);
        }
        return unflattenEqualityExpr(bandExpr.args, bandExpr.ops);
    }

    private static Expr build(SimpleCParser.EqualityExprContext equalityExpr) {
        if (equalityExpr.single != null) {
            return build(equalityExpr.single);
        }
        return unflattenRelExpr(equalityExpr.args, equalityExpr.ops);
    }

    private static Expr build(SimpleCParser.RelExprContext relExpr) {
        if (relExpr.single != null) {
            return build(relExpr.single);
        }
        return unflattenShiftExpr(relExpr.args, relExpr.ops);
    }

    private static Expr build(SimpleCParser.ShiftExprContext shiftExpr) {
        if (shiftExpr.single != null) {
            return build(shiftExpr.single);
        }
        return unflattenAddExpr(shiftExpr.args, shiftExpr.ops);
    }

    private static Expr build(SimpleCParser.AddExprContext addExpr) {
        if (addExpr.single != null) {
            return build(addExpr.single);
        }
        return unflattenMulExpr(addExpr.args, addExpr.ops);
    }

    private static Expr build(SimpleCParser.MulExprContext mulExpr) {
        if (mulExpr.single != null) {
            return build(mulExpr.single);
        }
        return unflattenUnaryExpr(mulExpr.args, mulExpr.ops);
    }

    private static Expr build(SimpleCParser.UnaryExprContext unaryExpr) {
        List<String> operators = unaryExpr.ops.stream().map(Token::getText).collect(Collectors.toList());
        if (unaryExpr.single != null) {
            return new UnaryExpr(build(unaryExpr.single), operators);
        } else {
            return new UnaryExpr(build(unaryExpr.arg), operators);
        }
    }

    private static Expr build(SimpleCParser.AtomExprContext atomExpr) {
        if (atomExpr.numberExpr() != null) {
            return new NumberExpr(atomExpr.numberExpr().NUMBER().toString());
        } else if (atomExpr.varrefExpr() != null) {
            return build(atomExpr.varrefExpr());
        } else if (atomExpr.parenExpr() != null) {
            return new ParenExpr(build(atomExpr.parenExpr().arg));
        } else if (atomExpr.resultExpr() != null) {
            return new ResultExpr(atomExpr.resultExpr().resultTok.getText());
        } else {
            return build(atomExpr.oldExpr());
        }
    }

    private static Expr build(SimpleCParser.VarrefExprContext varRefExpr) {
        return new VarRefExpr(build(varRefExpr.var));
    }

    private static VarRef build(SimpleCParser.VarrefContext varRef) {
        return new VarRef(varRef.ident.name.getText());
    }

    public static OldExpr build(SimpleCParser.OldExprContext oldExprContext) {
        return new OldExpr(build(oldExprContext.arg));
    }

    private static TernaryExpr unflattenTernaryExpr(List<SimpleCParser.LorExprContext> args) {
        if (args.size() == 3) {
            return new TernaryExpr(build(args.get(0)), build(args.get(1)), build(args.get(2)));
        }
        return new TernaryExpr(
            build(args.get(0)),
            build(args.get(1)),
            unflattenTernaryExpr(args.subList(2, args.size())));
    }

    private static BinaryExpr unflattenLandExpr(List<SimpleCParser.LandExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenLandExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }

    private static BinaryExpr unflattenBorExpr(List<SimpleCParser.BorExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenBorExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }

    private static BinaryExpr unflattenBxorExpr(List<SimpleCParser.BxorExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenBxorExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }

    private static BinaryExpr unflattenBandExpr(List<SimpleCParser.BandExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenBandExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }

    private static BinaryExpr unflattenEqualityExpr(List<SimpleCParser.EqualityExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenEqualityExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }

    private static BinaryExpr unflattenRelExpr(List<SimpleCParser.RelExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenRelExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }

    private static BinaryExpr unflattenShiftExpr(List<SimpleCParser.ShiftExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenShiftExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }

    private static BinaryExpr unflattenAddExpr(List<SimpleCParser.AddExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenAddExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }

    private static BinaryExpr unflattenMulExpr(List<SimpleCParser.MulExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenMulExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }

    private static BinaryExpr unflattenUnaryExpr(List<SimpleCParser.UnaryExprContext> args, List<Token> ops) {
        if (ops.size() == 1) {
            return new BinaryExpr(ops.get(0).getText(), build(args.get(0)), build(args.get(1)));
        }
        return new BinaryExpr(
            Iterables.getLast(ops).getText(),
            unflattenUnaryExpr(args.subList(0, args.size() - 1), ops.subList(0, ops.size() - 1)),
            build(Iterables.getLast(args)));
    }
}
