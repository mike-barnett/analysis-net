// Copyright (c) Edgardo Zoppi.  All Rights Reserved.  Licensed under the MIT License.  See License.txt in the project root for license information.

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Backend.ThreeAddressCode.Instructions;
using Backend.ThreeAddressCode.Values;
using Backend.Visitors;
using Microsoft.Cci;
using Backend.Utils;

namespace Backend.Analysis
{
	public class TypeInferenceAnalysis
	{
		#region class TypeInferencer

		private class TypeInferencer : InstructionVisitor
		{
            private Dictionary<IVariable, ITypeReference> polymorphicVariables = new Dictionary<IVariable, ITypeReference>();

            public override void Visit(IInstructionContainer container)
            {
                base.Visit(container);

                // null variables that were never used should have (default) type System.Object
                for (int i = 0; i < polymorphicVariables.Keys.Count; i++)
                {
                    var v = polymorphicVariables.Keys.ElementAt(i);
                    if (v.Type == null)
                        v.Type = polymorphicVariables[v];
                }
            }

            public override void Visit(LocalAllocationInstruction instruction)
			{
				instruction.TargetAddress.Type = Types.Instance.NativePointerType;
			}

			public override void Visit(SizeofInstruction instruction)
			{
				instruction.Result.Type = Types.Instance.SizeofType;
			}

			public override void Visit(CreateArrayInstruction instruction)
			{
				instruction.Result.Type = Types.Instance.ArrayType(instruction.ElementType, instruction.Rank);
			}

			public override void Visit(CatchInstruction instruction)
			{
				instruction.Result.Type = instruction.ExceptionType;
			}

			public override void Visit(CreateObjectInstruction instruction)
			{
				instruction.Result.Type = instruction.Constructor.ContainingType;
			}

			public override void Visit(MethodCallInstruction instruction)
			{
				if (instruction.HasResult)
				{
					instruction.Result.Type = instruction.Method.Type;
				}
			}

			public override void Visit(IndirectMethodCallInstruction instruction)
			{
				if (instruction.HasResult)
				{
					instruction.Result.Type = instruction.Function.Type;
				}
			}

			public override void Visit(LoadInstruction instruction)
			{
                // null is polymorphic so we handle it specially. We don't set the
                // corresponding variable's type yet. We postpone it to usage of the variable
                // or set it to System.Object if it is never used.
                if (instruction.Operand is ThreeAddressCode.Values.Constant &&
                    (instruction.Operand as ThreeAddressCode.Values.Constant).Value == null)
                {
                    polymorphicVariables[instruction.Result] = instruction.Operand.Type;
                }
                // if we have variable to variable assignment where the result was assigned
                // a type but the operand was not, then we set the operand type accordingly.
                else if (instruction.Result.Type != null && instruction.Operand is IVariable 
                            && (instruction.Operand as IVariable).Type == null)
                {
                    (instruction.Operand as IVariable).Type = instruction.Result.Type;
                }
                else
                {
                    instruction.Result.Type = instruction.Operand.Type;
                }
			}

			public override void Visit(LoadTokenInstruction instruction)
			{
				instruction.Result.Type = Types.Instance.TokenType(instruction.Token);
			}

			public override void Visit(StoreInstruction instruction)
			{
                // Set the null variable a type.
                if (instruction.Operand.Type == null && polymorphicVariables.ContainsKey(instruction.Operand))
                {
                    instruction.Operand.Type = instruction.Result.Type;
                    polymorphicVariables.Remove(instruction.Operand);
                }
			}

			public override void Visit(UnaryInstruction instruction)
			{
				instruction.Result.Type = instruction.Operand.Type;
			}

			public override void Visit(ConvertInstruction instruction)
			{
				var type = instruction.Operand.Type;

				switch (instruction.Operation)
				{
					case ConvertOperation.Cast:
					case ConvertOperation.Box:
					case ConvertOperation.Unbox:
						// ConversionType is the data type of the result
						type = instruction.ConversionType;
						break;

					case ConvertOperation.UnboxPtr:
						// Pointer to ConversionType is the data type of the result
						type = Types.Instance.PointerType(instruction.ConversionType);
						break;
				}

				instruction.Result.Type = type;
			}

			public override void Visit(PhiInstruction instruction)
			{
				var type = instruction.Arguments.First().Type;
				var arguments = instruction.Arguments.Skip(1);

				foreach (var argument in arguments)
				{
					type = TypeHelper.MergedType(type, argument.Type);
				}

				instruction.Result.Type = type;
			}

			public override void Visit(BinaryInstruction instruction)
			{
				var left = instruction.LeftOperand.Type;

				var right = instruction.RightOperand.Type;
				var unsigned = instruction.UnsignedOperands;

				switch (instruction.Operation)
				{
					case BinaryOperation.Add:
					case BinaryOperation.Div:
					case BinaryOperation.Mul:
					case BinaryOperation.Rem:
					case BinaryOperation.Sub:
						instruction.Result.Type = Types.Instance.BinaryNumericOperationType(left, right, unsigned);
						break;

					case BinaryOperation.And:
					case BinaryOperation.Or:
					case BinaryOperation.Xor:
						instruction.Result.Type = Types.Instance.BinaryLogicalOperationType(left, right);
						break;

					case BinaryOperation.Shl:
					case BinaryOperation.Shr:
						instruction.Result.Type = left;
						break;
						
					case BinaryOperation.Eq:
					case BinaryOperation.Gt:
					case BinaryOperation.Lt:
						instruction.Result.Type = Types.Instance.PlatformType.SystemBoolean;
						break;
				}
			}
		}

		#endregion

		private ControlFlowGraph cfg;

		public TypeInferenceAnalysis(ControlFlowGraph cfg)
		{
			this.cfg = cfg;
		}

		public void Analyze()
		{
			var inferer = new TypeInferencer();
			var sorted_nodes = cfg.ForwardOrder;

            var fixedPoint = GetTypeInferenceResult(true);
            while (true)
            {
                for (var i = 0; i < sorted_nodes.Length; ++i)
                {
                    var node = sorted_nodes[i];
                    try
                    {
                        inferer.Visit(node);
                    }
                    catch { }
                }

                if (FixedPointReached(fixedPoint))
                    break;
                else
                {
                    fixedPoint = GetTypeInferenceResult();
                }
            }         
		}


        private Dictionary<IVariable, ITypeReference> GetTypeInferenceResult(bool start = false)
        {
            var vars = cfg.GetVariables();
            var result = new Dictionary<IVariable, ITypeReference>();
            foreach(var v in vars)
            {
                if (start)
                    result[v] = null;
                else
                    result[v] = v.Type;
            }
            return result;
        }

        private bool FixedPointReached(Dictionary<IVariable, ITypeReference> prev)
        {
            var vars = cfg.GetVariables();
            foreach (var v in vars)
            {
                // this covers null == null also
                if (prev[v] == v.Type)
                    continue;

                if (prev[v] == null || v.Type == null)
                    return false;

                // double-check
                if (!Microsoft.Cci.TypeHelper.TypesAreEquivalent(prev[v], v.Type, true))
                    return false;
            }
            return true;
        }
        


    }
}
