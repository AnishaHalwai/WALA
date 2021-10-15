package com.ibm.wala.cast.java.test; /*
                                      * Copyright (c) 2002 - 2006 IBM Corporation.
                                      * All rights reserved. This program and the accompanying materials
                                      * are made available under the terms of the Eclipse Public License v1.0
                                      * which accompanies this distribution, and is available at
                                      * http://www.eclipse.org/legal/epl-v10.html
                                      *
                                      * Contributors:
                                      *     IBM Corporation - initial API and implementation
                                      */

import com.ibm.wala.cast.ir.ssa.AstIRFactory;
import com.ibm.wala.cast.java.ExceptionPruningAnalysis;
import com.ibm.wala.cast.java.InterprocAnalysisResult;
import com.ibm.wala.cast.java.NullPointerAnalysis;
import com.ibm.wala.cast.java.client.impl.ZeroOneContainerCFABuilderFactory;
import com.ibm.wala.cast.java.intra.IntraprocNullPointerAnalysis;
import com.ibm.wala.cast.java.intra.NullPointerState.State;
import com.ibm.wala.cast.java.ipa.callgraph.JavaSourceAnalysisScope;
import com.ibm.wala.cast.java.translator.jdt.ecj.ECJClassLoaderFactory;
import com.ibm.wala.cast.loader.AstMethod;
import com.ibm.wala.cast.tree.CAstSourcePositionMap.Position;
import com.ibm.wala.cast.util.SourceBuffer;
import com.ibm.wala.classLoader.ClassLoaderFactory;
import com.ibm.wala.classLoader.SourceDirectoryTreeModule;
import com.ibm.wala.classLoader.SourceFileModule;
import com.ibm.wala.core.util.strings.StringStuff;
import com.ibm.wala.core.util.warnings.Warnings;
import com.ibm.wala.ipa.callgraph.AnalysisCacheImpl;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilder;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.IAnalysisCacheView;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.properties.WalaProperties;
import com.ibm.wala.ssa.DefUse;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAOptions;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.NullProgressMonitor;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.graph.GraphIntegrity.UnsoundGraphException;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Vector;
import java.util.jar.JarFile;
import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;

/**
 * Test validity and precision of inter-procedural NullpointerException-Analysis {@link
 * IntraprocNullPointerAnalysis}
 */
public class NullPointerExceptionInterTest {

  private static AnalysisScope scope;

  private static ClassHierarchy cha;

  private static CallGraph cg;

  private static IAnalysisCacheView cache;

  protected static ClassLoaderFactory getLoaderFactory(AnalysisScope scope) {
    return new ECJClassLoaderFactory(scope.getExclusions());
  }

  protected static Iterable<Entrypoint> getEntrypoints(String mainClass, IClassHierarchy cha) {
    Iterable<Entrypoint> entrypoints =
        Util.makeMainEntrypoints(JavaSourceAnalysisScope.SOURCE, cha, new String[] {mainClass});
    return entrypoints;
  }

  @BeforeClass
  public static void beforeClass() throws Exception {
    scope = new JavaSourceAnalysisScope();
    String sourceDir = "/Users/anisha/WALA/com.ibm.wala.core/src/testSubjects/java/cfg/exc";
    String[] stdlibs = WalaProperties.getJ2SEJarFiles();
    for (String stdlib : stdlibs) {
      scope.addToScope(ClassLoaderReference.Primordial, new JarFile(stdlib));
    }
    // add the source directory
    File root = new File(sourceDir);
    if (root.isDirectory()) {
      scope.addToScope(JavaSourceAnalysisScope.SOURCE, new SourceDirectoryTreeModule(root));
    } else {
      String srcFileName = sourceDir.substring(sourceDir.lastIndexOf(File.separator) + 1);
      assert root.exists() : "couldn't find " + sourceDir;
      scope.addToScope(
          JavaSourceAnalysisScope.SOURCE, new SourceFileModule(root, srcFileName, null));
    }
    cha = ClassHierarchyFactory.make(scope, getLoaderFactory(scope));
    Iterable<Entrypoint> entrypoints = getEntrypoints("Lcfg/exc/inter/CallFieldAccess", cha);
    AnalysisOptions options = new AnalysisOptions(scope, entrypoints);
    options.setEntrypoints(entrypoints);
    options
        .getSSAOptions()
        .setDefaultValues(
            new SSAOptions.DefaultValues() {
              @Override
              public int getDefaultValue(SymbolTable symtab, int valueNumber) {
                return symtab.getDefaultValue(valueNumber);
              }
            });
    // you can dial down reflection handling if you like
    options.setReflectionOptions(AnalysisOptions.ReflectionOptions.NONE);
    cache = new AnalysisCacheImpl(AstIRFactory.makeDefaultFactory(), options.getSSAOptions());
    //
    //    ClassLoaderFactory factory = new ClassLoaderFactoryImpl(scope.getExclusions());
    try {
      cha = ClassHierarchyFactory.make(scope, getLoaderFactory(scope));
      CallGraphBuilder<?> builder =
          new ZeroOneContainerCFABuilderFactory().make(options, cache, cha);
      cg = builder.makeCallGraph(options, null);
      System.err.println(cg);
    } catch (ClassHierarchyException e) {
      throw new Exception(e);
    }
  }

  @AfterClass
  public static void afterClass() throws Exception {
    Warnings.clear();
    scope = null;
    cha = null;
    cg = null;
    cache = null;
  }

  @Ignore
  @Test
  public void testIfException() throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callIfException()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }

  @Ignore
  @Test
  public void testDynamicIfException()
      throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicIfException()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }

  @Ignore
  @Test
  public void testIfNoException() throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callIfNoException()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);
    Assert.assertFalse(intraExplodedCFG.hasExceptions());
  }

  @Ignore
  @Test
  public void testDynamicIfNoException()
      throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicIfNoException()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);
    Assert.assertFalse(intraExplodedCFG.hasExceptions());
  }

  @Ignore
  @Test
  public void testIf2Exception() throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callIf2Exception()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }

  @Ignore
  @Test
  public void testDynamicIf2Exception()
      throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicIf2Exception()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }

  @Ignore
  @Test
  public void testIf2NoException() throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callIf2NoException()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);
    Assert.assertFalse(intraExplodedCFG.hasExceptions());
  }

  @Ignore
  @Test
  public void testDynamicIf2NoException()
      throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicIf2NoException()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);
    Assert.assertFalse(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testGetException()
      throws UnsoundGraphException, CancelException, WalaException, IOException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callGetException()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
    printStuff(callNode, intraExplodedCFG);
  }

  @Test
  public void testDynamicGetException()
      throws UnsoundGraphException, CancelException, WalaException, IOException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicGetException()Lcfg/exc/intra/B",
            JavaSourceAnalysisScope.SOURCE);

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());

    printStuff(callNode, intraExplodedCFG);
  }

  public void printStuff(
      CGNode callNode,
      ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG)
      throws IOException {
    IR ir = callNode.getIR();
    DefUse du = callNode.getDU();
    SymbolTable st = ir.getSymbolTable();

    for (int i = 1; i <= st.getMaxValueNumber(); i++) {
      SSAInstruction inst = du.getDef(i);

      if (inst != null && inst.getDef() != -1) {
        IExplodedBasicBlock bb = intraExplodedCFG.getCFG().getBlockForInstruction(inst.iIndex());
        State s = intraExplodedCFG.getState(bb).getState(inst.getDef());

        AstMethod asm = (AstMethod) callNode.getMethod();
        String[][] names = asm.debugInfo().getSourceNamesForValues();
        System.err.println(
            ""
                + Arrays.toString(names[inst.getDef()])
                + new SourceBuffer(asm.debugInfo().getInstructionPosition(inst.iIndex()))
                + " "
                + s);
        if (inst instanceof SSAAbstractInvokeInstruction) {
          SSAAbstractInvokeInstruction saa = (SSAAbstractInvokeInstruction) inst;

          for (int j = 0; j < saa.getNumberOfPositionalParameters(); j++) {
            Position p = asm.debugInfo().getOperandPosition(inst.iIndex(), j);
            System.err.println("" + new SourceBuffer(p));
          }
        }
        ir.iterateAllInstructions()
            .forEachRemaining(
                inst2 -> {
                  if (inst2.iIndex() >= 0)
                    try {
                      System.err.println("------code to test extractComments-------");
                      //
                      // System.err.println(asm.debugInfo().getLeadingComment(inst.iIndex()));
                      int pind = inst2.iIndex();

                      String str = asm.debugInfo().getFollowingComment(pind);
                      String str2 = asm.debugInfo().getLeadingComment(pind);
                      System.err.println(""+ new SourceBuffer(asm.debugInfo().getInstructionPosition(pind)));
                      System.err.println("Following at: "+pind+" "+str);
                      System.err.println("Leading at: "+pind+" "+str2);
                    } catch (Exception e) {
                    }
                });
      }
      //      AstMethod asm2 = (AstMethod)callNode.getMethod();
      //      String[][] names2 = asm2.debugInfo().
    }
    //    intraExplodedCFG.getCFG().forEach(bb -> {
    //      NullPointerState s = intraExplodedCFG.getState(bb);
    //      System.err.println(s.toString());
    //    });

  }

  public List<String> extractComment(String allInstructions) {
    // focusing on extracting comments starting with '//'
    // index i = find first occurence of '\\'
    // if found, find first occurence of next line,
    // if not found, break
    // index j =if next line not found, return whole string after '\\', break
    // store that substring[i to j] in list
    // repeat with allInstructions = allInstructions[j:]

    List<String> allComments = new Vector<>();

    while (true) {
      if (allInstructions.length() <= 2) break;

      int i = allInstructions.indexOf("//");
      if (i == -1) {
        //        System.err.println("no comments found\n");
        break;
      }

      int j = allInstructions.indexOf("\n", i);
      if (j == -1) {
        allComments.add(allInstructions);
        System.err.println(allInstructions);
        break;
      }
      allComments.add(allInstructions.substring(i, j));
      //      System.err.println(allInstructions.substring(i,j));
      allInstructions = allInstructions.substring(j + 1);
    }

    return allComments;
  }
}
// TODO 0:
// explore:
// what else in debugInfo, anything useful?
// []fad.testGet(unknown, b) BOTH
// list of args 0: fad, 1:unknown, 2:b
// debugInfo has method to get args --- explore?!?!
// getOperandPosition(instruction index, operand index (0,1,2))

// TODO 1:
// create method extractComment: parameter: string chunk, returns: list of comment strings
