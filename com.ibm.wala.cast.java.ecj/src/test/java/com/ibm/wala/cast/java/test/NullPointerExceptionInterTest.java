package com.ibm.wala.cast.java.test;/*
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
import com.ibm.wala.cast.java.client.impl.ZeroOneContainerCFABuilderFactory;
import com.ibm.wala.cast.java.ipa.callgraph.JavaSourceAnalysisScope;
import com.ibm.wala.cast.java.translator.jdt.ecj.ECJClassLoaderFactory;
import com.ibm.wala.cast.java.ExceptionPruningAnalysis;
import com.ibm.wala.cast.java.InterprocAnalysisResult;
import com.ibm.wala.cast.java.NullPointerAnalysis;
import com.ibm.wala.cast.java.intra.IntraprocNullPointerAnalysis;
import com.ibm.wala.classLoader.ClassLoaderFactory;
import com.ibm.wala.classLoader.ClassLoaderFactoryImpl;
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
import java.util.jar.JarFile;
import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.BeforeClass;
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
    ClassLoaderFactory factory = new ClassLoaderFactoryImpl(scope.getExclusions());
    try {
      cha = ClassHierarchyFactory.make(scope, getLoaderFactory(scope));
      CallGraphBuilder<?> builder =
          new ZeroOneContainerCFABuilderFactory().make(options, cache, cha);
      cg = builder.makeCallGraph(options, null);
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

  @Test
  public void testIfException() throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callIfException()Lcfg/exc/intra/B");

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testDynamicIfException()
      throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicIfException()Lcfg/exc/intra/B");

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testIfNoException() throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callIfNoException()Lcfg/exc/intra/B");

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);
    Assert.assertFalse(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testDynamicIfNoException()
      throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicIfNoException()Lcfg/exc/intra/B");

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);
    Assert.assertFalse(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testIf2Exception() throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callIf2Exception()Lcfg/exc/intra/B");

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testDynamicIf2Exception()
      throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicIf2Exception()Lcfg/exc/intra/B");

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testIf2NoException() throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callIf2NoException()Lcfg/exc/intra/B");

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);
    Assert.assertFalse(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testDynamicIf2NoException()
      throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicIf2NoException()Lcfg/exc/intra/B");

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);
    Assert.assertFalse(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testGetException() throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callGetException()Lcfg/exc/intra/B");

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }

  @Test
  public void testDynamicGetException()
      throws UnsoundGraphException, CancelException, WalaException {
    MethodReference mr =
        StringStuff.makeMethodReference(
            "cfg.exc.inter.CallFieldAccess.callDynamicGetException()Lcfg/exc/intra/B");

    Assert.assertEquals(1, cg.getNodes(mr).size());
    final CGNode callNode = cg.getNodes(mr).iterator().next();

    InterprocAnalysisResult<SSAInstruction, IExplodedBasicBlock> interExplodedCFG =
        NullPointerAnalysis.computeInterprocAnalysis(cg, new NullProgressMonitor());

    ExceptionPruningAnalysis<SSAInstruction, IExplodedBasicBlock> intraExplodedCFG =
        interExplodedCFG.getResult(callNode);

    Assert.assertTrue(intraExplodedCFG.hasExceptions());
  }
}