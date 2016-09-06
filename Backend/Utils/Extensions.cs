﻿// Copyright (c) Edgardo Zoppi.  All Rights Reserved.  Licensed under the MIT License.  See License.txt in the project root for license information.

using Backend.Analysis;
using Backend.ThreeAddressCode;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Backend.ThreeAddressCode.Values;
using Backend.ThreeAddressCode.Expressions;
using Backend.ThreeAddressCode.Instructions;
using Backend.Visitors;
using Microsoft.Cci;

namespace Backend.Utils
{
	public static class Extensions
	{
		public static bool DictionaryEquals<K,V>(this IDictionary<K,V> self, IDictionary<K,V> other, Func<V, V, bool> valueEquals = null)
		{
			if (object.ReferenceEquals(self, other)) return true;
			if (self.Count != other.Count) return false;

			if (valueEquals == null)
			{
				valueEquals = (a, b) => object.Equals(a, b);
			}

			foreach (var key in self.Keys)
			{
				var otherContainsKey = other.ContainsKey(key);
				if (!otherContainsKey) return false;
			}

			foreach (var entry in self)
			{
				var value = other[entry.Key];
				var valuesAreEquals = valueEquals(entry.Value, value);

				if (!valuesAreEquals) return false;
			}

			return true;
		}

		public static void AddRange<T>(this ICollection<T> collection, IEnumerable<T> elements)
		{
			foreach (var element in elements)
			{
				collection.Add(element);
			}
		}

		public static MapSet<K, V> ToMapSet<K, V>(this IEnumerable<V> elements, Func<V, K> keySelector)
		{
			var result = new MapSet<K, V>();

			foreach (var element in elements)
			{
				var key = keySelector(element);
				result.Add(key, element);
			}

			return result;
		}

		public static MapList<K, V> ToMapList<K, V>(this IEnumerable<V> elements, Func<V, K> keySelector)
		{
			var result = new MapList<K, V>();

			foreach (var element in elements)
			{
				var key = keySelector(element);
				result.Add(key, element);
			}

			return result;
		}

		public static Subset<T> ToSubset<T>(this T[] universe)
		{
			return new Subset<T>(universe, false);
		}

		public static Subset<T> ToEmptySubset<T>(this T[] universe)
		{
			return new Subset<T>(universe, true);
		}

		public static ISet<IVariable> GetVariables(this IInstructionContainer block)
		{
			var result = from i in block.Instructions
						 from v in i.Variables
						 select v;

			//var result = block.Instructions.SelectMany(i => i.Variables);
			return new HashSet<IVariable>(result);
		}

		public static ISet<IVariable> GetModifiedVariables(this IInstructionContainer block)
		{
			var result = from i in block.Instructions
						 from v in i.ModifiedVariables
						 select v;

			//var result = block.Instructions.SelectMany(i => i.ModifiedVariables);
			return new HashSet<IVariable>(result);
		}

		public static ISet<IVariable> GetUsedVariables(this IInstructionContainer block)
		{
			var result = from i in block.Instructions
						 from v in i.UsedVariables
						 select v;

			//var result = block.Instructions.SelectMany(i => i.UsedVariables);
			return new HashSet<IVariable>(result);
		}

		public static ISet<IVariable> GetDefinedVariables(this IInstructionContainer block)
		{
			var result = from i in block.Instructions
						 let d = i as DefinitionInstruction
						 where d != null && d.HasResult
						 select d.Result;

			return new HashSet<IVariable>(result);
			//var result = new HashSet<IVariable>();

			//foreach (var instruction in block.Instructions)
			//{
			//    var definition = instruction as DefinitionInstruction;

			//    if (definition != null && definition.HasResult)
			//    {
			//        result.Add(definition.Result);
			//    }
			//}

			//return result;
		}

		public static ISet<IVariable> GetModifiedVariables(this CFGLoop loop)
		{
			var result = from n in loop.Body
						 from v in n.GetModifiedVariables()
						 select v;

			//var result = loop.Body.SelectMany(n => n.GetModifiedVariables());
			return new HashSet<IVariable>(result);
		}

		public static ISet<IVariable> GetVariables(this ControlFlowGraph cfg)
		{
			var result = from n in cfg.Nodes
						 from v in n.GetVariables()
						 select v;

			//var result = cfg.Nodes.SelectMany(n => n.GetVariables());
			return new HashSet<IVariable>(result);
		}

		public static ISet<CFGNode> GetExitNodes(this CFGLoop loop)
		{
			var result = from n in loop.Body
						 from m in n.Successors
						 where !loop.Body.Contains(m)
						 select n;

			//var result = loop.Body.Where(n => n.Successors.Any(m => !loop.Body.Contains(m)));
			return new HashSet<CFGNode>(result);
		}

		public static IExpression ToExpression(this IValue value)
		{
			return value as IExpression;
		}

		//public static IExpression GetValueOriginal(this IDictionary<IVariable, IExpression> equalities, IVariable variable)
		//{
		//    var result = equalities.ContainsKey(variable) ? equalities[variable] : variable;
		//    return result;
		//}
		
		public static IExpression GetValue(this IDictionary<IVariable, IExpression> equalities, IVariable variable)
		{
			IExpression result = variable;

			while (variable != null && equalities.ContainsKey(variable))
			{
				result = equalities[variable];
				variable = result as IVariable;
			}

			return result;
		}

		public static bool IsTemporal(this IVariable variable)
		{
			while (variable is DerivedVariable)
			{
				var derived = variable as DerivedVariable;
				variable = derived.Original;
			}

			var result = variable is TemporalVariable;
			return result;
		}

		public static bool IsCopy(this Instruction instruction, out IVariable left, out IVariable right)
		{
			var result = false;
			left = null;
			right = null;

			if (instruction is LoadInstruction)
			{
				var load = instruction as LoadInstruction;

				if (load.Operand is IVariable)
				{
					left = load.Result;
					right = load.Operand as IVariable;
					result = true;
				}
			}

			return result;
		}

		public static IExpression ReplaceVariables<T>(this IExpression expr, IDictionary<IVariable, T> equalities) where T : IExpression
		{
			foreach (var variable in expr.Variables)
			{
				if (variable.IsTemporal())
				{
					var hasValue = equalities.ContainsKey(variable);

					if (hasValue)
					{
						var value = equalities[variable];
						var isUnknown = value is UnknownValue;
						var isPhi = value is PhiExpression;
						var isMethodCall = value is MethodCallExpression;

						if (isUnknown || isPhi || isMethodCall)
							continue;

						expr = expr.Replace(variable, value);
					}
				}
			}

			return expr;
		}

		public static void RemoveTemporalVariables(this PointsToGraph ptg)
		{
			var temporals = ptg.Variables.OfType<TemporalVariable>().ToArray();

			foreach (var temporal in temporals)
			{
				ptg.Remove(temporal);
			}
		}

		public static bool IsPure(this IMethodReference method)
		{
			var result = method.Attributes.Any(a => a.Type == Types.Instance.PureAttributeType);

			if (!result)
			{
				result = method.Name.Value == "get_Count" && Types.Instance.IsContainer(method.ContainingType);
			}

			return result;
		}

        public static void RemoveAll<T>(this ICollection<T> self, IEnumerable<T> elements)
        {
            foreach (var element in elements)
            {
                self.Remove(element);
            }
        }

        public static void SetRange<K, V>(this IDictionary<K, V> self, IEnumerable<KeyValuePair<K, V>> elements)
        {
            foreach (var element in elements)
            {
                self[element.Key] = element.Value;
            }
        }

        public static IDictionary<K, V> Intersect<K, V>(this IDictionary<K, V> self, IEnumerable<KeyValuePair<K, V>> other, Func<V, V, V> valueIntersect)
        {
            var result = new Dictionary<K, V>();

            foreach (var entry in other)
            {
                V value;

                if (self.TryGetValue(entry.Key, out value))
                {
                    value = valueIntersect(value, entry.Value);

                    if (value != null)
                    {
                        result.Add(entry.Key, value);
                    }
                }
            }

            return result;
        }

        public static void IntersectWith<K, V>(this IDictionary<K, V> self, IEnumerable<KeyValuePair<K, V>> other, Func<V, V, V> valueIntersect)
        {
            var keys = new HashSet<K>();

            foreach (var entry in other)
            {
                V value;

                if (self.TryGetValue(entry.Key, out value))
                {
                    value = valueIntersect(value, entry.Value);

                    if (value != null)
                    {
                        self[entry.Key] = value;
                        keys.Add(entry.Key);
                    }
                    else
                    {
                        self.Remove(entry.Key);
                    }
                }
            }

            var keysToRemove = self.Keys.Except(keys).ToArray();

            foreach (var key in keysToRemove)
            {
                self.Remove(key);
            }
        }

    }
}
