#!/usr/bin/env ruby
# frozen_string_literal: true

require "json"
require "yaml"

ROOT = File.expand_path("..", __dir__)
METADATA = File.join(ROOT, "formalization.yaml")
COMPARATOR = File.join(ROOT, "comparator.json")
CHALLENGE = File.join(ROOT, "Challenge.lean")
ALLOWED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"].freeze
ALLOWED_CONFIG_KEYS = %w[
  challenge_module solution_module theorem_names permitted_axioms
  definition_names enable_nanoda
].freeze

def fail_check(message)
  warn "error: #{message}"
  exit 1
end

metadata_text = File.binread(METADATA).force_encoding(Encoding::UTF_8)
fail_check("formalization.yaml is not valid UTF-8") unless metadata_text.valid_encoding?
fail_check("formalization.yaml still contains TEMPLATE text") if metadata_text.include?("TEMPLATE")

metadata = YAML.safe_load(
  metadata_text,
  permitted_classes: [],
  permitted_symbols: [],
  aliases: false
)
fail_check("formalization.yaml must contain one mapping") unless metadata.is_a?(Hash)
fail_check("metadata version must be v0.4") unless metadata["version"] == "v0.4"

project = metadata["project"]
fail_check("project must be a mapping") unless project.is_a?(Hash)
%w[name description license].each do |field|
  value = project[field]
  fail_check("project.#{field} must be nonempty text") unless value.is_a?(String) && !value.strip.empty?
end
fail_check("project.license must be Apache-2.0") unless project["license"] == "Apache-2.0"
%w[authors responsible_maintainers].each do |field|
  value = project[field]
  valid = value.is_a?(Array) && !value.empty? &&
    value.all? { |item| item.is_a?(String) && !item.strip.empty? }
  fail_check("project.#{field} must be a nonempty list of human names") unless valid
end

classification = metadata["classification"]
fail_check("classification must be a mapping") unless classification.is_a?(Hash)
arxiv = classification["arxiv"]
fail_check("classification.arxiv must be nonempty") unless arxiv.is_a?(Array) && !arxiv.empty?

sources = metadata["sources"]
fail_check("sources must be a nonempty list") unless sources.is_a?(Array) && !sources.empty?
source_based = false
sources.each_with_index do |source, index|
  fail_check("sources[#{index}] must be a mapping") unless source.is_a?(Hash)
  title = source["title"]
  relationship = source["relationship"]
  fail_check("sources[#{index}].title must be nonempty") unless title.is_a?(String) && !title.strip.empty?
  allowed = %w[formalizes adapts independently-proves background other]
  fail_check("sources[#{index}].relationship is invalid") unless allowed.include?(relationship)
  source_based ||= %w[formalizes adapts independently-proves].include?(relationship)
end
fail_check("sources do not identify a source-based result") unless source_based

methods = metadata.dig("automation", "methods")
valid_methods = methods.is_a?(Array) && !methods.empty? && methods.all? do |method|
  method.is_a?(Hash) && method["method"].is_a?(String) && !method["method"].strip.empty?
end
fail_check("automation.methods must be a nonempty method list") unless valid_methods

review_status = metadata.dig("review", "status")
fail_check("review.status must be nonempty") unless review_status.is_a?(String) && !review_status.strip.empty?

license_text = File.binread(File.join(ROOT, "LICENSE"))
fail_check("LICENSE is not the Apache License 2.0 text") unless
  license_text.include?("Apache License") && license_text.include?("Version 2.0, January 2004")

config = JSON.parse(File.read(COMPARATOR, encoding: "UTF-8"))
fail_check("comparator.json must contain one object") unless config.is_a?(Hash)
unknown = config.keys - ALLOWED_CONFIG_KEYS
fail_check("comparator.json has unknown keys: #{unknown.join(', ')}") unless unknown.empty?
%w[challenge_module solution_module theorem_names permitted_axioms].each do |field|
  fail_check("comparator.json is missing #{field}") unless config.key?(field)
end
fail_check("challenge_module must be Challenge") unless config["challenge_module"] == "Challenge"
fail_check("solution_module must be Solution") unless config["solution_module"] == "Solution"
theorems = config["theorem_names"]
fail_check("theorem_names must contain four declarations") unless
  theorems.is_a?(Array) && theorems.length == 4 && theorems.uniq.length == 4
definitions = config["definition_names"]
fail_check("definition_names must be empty because Dedekind psi has a concrete Challenge value") unless
  definitions == []
axioms = config["permitted_axioms"]
fail_check("permitted_axioms contains a nonstandard axiom") unless
  axioms.is_a?(Array) && axioms.all? { |axiom| ALLOWED_AXIOMS.include?(axiom) }
fail_check("enable_nanoda must be true") unless config["enable_nanoda"] == true

challenge_text = File.binread(CHALLENGE).force_encoding(Encoding::UTF_8)
fail_check("Challenge.lean is not valid UTF-8") unless challenge_text.valid_encoding?
fail_check("Challenge.lean exceeds 100 KiB") if challenge_text.bytesize > 100 * 1024
fail_check("Challenge.lean exceeds 1,000 lines") if challenge_text.lines.length > 1_000
sorry_lines = challenge_text.lines.count { |line| line.match?(/^\s+sorry\s*$/) }
fail_check("Challenge.lean must contain exactly four deliberate sorry bodies") unless sorry_lines == 4

puts "Palomar metadata, Comparator configuration, licence, and Challenge surface pass local checks."
