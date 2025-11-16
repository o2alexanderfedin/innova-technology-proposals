---
description: Update project context files with new information
argument-hint: [context-file]
allowed-tools: Read, Write
---

# Update Project Context

You are executing the `/update-context` command to update a context file.

## Purpose

Update context files (client-info, company-profile, or industry-background) with new information while preserving structure and format.

## Steps to Execute

### Step 1: Validate Argument

Check $1 is one of: client-info, company-profile, industry-background
If invalid, ERROR with list of valid options.

### Step 2: Read Current Context

Use Read tool to load context/$1.md
Display current content to user for reference.

### Step 3: Prompt for Updates

Ask user what they'd like to update:
- Add new information
- Modify existing content
- Complete incomplete sections

### Step 4: Collect User Input

Gather new information from user through conversation.
Ensure quality and completeness.

### Step 5: Update Context File

Use Write tool to update context/$1.md
Preserve markdown structure and headings.
Integrate new information appropriately.

### Step 6: Validate Update

Verify:
- File is valid markdown
- Key sections still present
- Content is substantive (>200 words for core sections)

### Step 7: Output Confirmation

Display success message with summary of changes.

## Success Criteria

- Context file updated with valid markdown
- Structure preserved
- New information integrated
- File remains readable and well-organized

## Error Handling

If $1 invalid:
```
ERROR: Invalid context file

Valid options: client-info, company-profile, industry-background
Usage: /update-context [context-file]
Example: /update-context company-profile
```

If context file doesn't exist:
```
ERROR: Context file not found: context/$1.md
Run /init-project first to create context templates.
```

## Expected Output

User receives confirmation of successful update with summary of changes made.
